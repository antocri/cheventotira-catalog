#!/usr/bin/env python3
"""
Genera il catalogo spiagge di CalaGiusta a partire da OpenStreetMap (Overpass API).

Per ogni spiaggia calcola automaticamente:
  - orientation : verso dove guarda il mare aperto (gradi bussola)
  - shelter     : quanto la baia e' chiusa (0 = aperta, 1 = cala stretta)
  - confidence  : quanto e' affidabile il calcolo

Il trucco per l'orientamento: in OpenStreetMap le linee `natural=coastline` sono
ORIENTATE con la terra a sinistra e il mare a destra. Quindi la direzione del mare
aperto e' semplicemente il bearing del segmento di costa + 90 gradi. Facendo la media
circolare dei segmenti vicini alla spiaggia si ottiene l'orientamento; quanto quei
segmenti "sventagliano" dice quanto la baia e' chiusa.

Uso:
    python3 build_catalog.py --out ../dist
    python3 build_catalog.py --bbox 36.0 14.0 38.5 16.5 --out ../dist   # solo Sicilia orientale

Solo libreria standard. Nessuna dipendenza.
"""

import argparse
import hashlib
import json
import math
import os
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
from datetime import datetime, timezone

OVERPASS_ENDPOINTS = [
    "https://overpass-api.de/api/interpreter",
    "https://overpass.kumi.systems/api/interpreter",
]

# Italia continentale + isole
DEFAULT_BBOX = (35.3, 6.4, 47.3, 18.7)  # south, west, north, east

TILE_DEG = 1.0
SEARCH_RADIUS_M = 800.0     # raggio entro cui cercare la costa attorno alla spiaggia
MIN_CONFIDENCE = 0.25       # sotto questa soglia l'orientamento non e' affidabile
DEDUPE_M = 120.0

EARTH_R = 6371000.0


# --------------------------------------------------------------------------- geometria


def to_local(lat, lon, lat0):
    """Proiezione equirettangolare locale in metri."""
    x = math.radians(lon) * math.cos(math.radians(lat0)) * EARTH_R
    y = math.radians(lat) * EARTH_R
    return x, y


def haversine(lat1, lon1, lat2, lon2):
    p1, p2 = math.radians(lat1), math.radians(lat2)
    dp = p2 - p1
    dl = math.radians(lon2 - lon1)
    a = math.sin(dp / 2) ** 2 + math.cos(p1) * math.cos(p2) * math.sin(dl / 2) ** 2
    return 2 * EARTH_R * math.asin(math.sqrt(a))


def bearing(lat1, lon1, lat2, lon2):
    """Direzione bussola da 1 a 2, 0-360."""
    p1, p2 = math.radians(lat1), math.radians(lat2)
    dl = math.radians(lon2 - lon1)
    y = math.sin(dl) * math.cos(p2)
    x = math.cos(p1) * math.sin(p2) - math.sin(p1) * math.cos(p2) * math.cos(dl)
    return (math.degrees(math.atan2(y, x)) + 360.0) % 360.0


def point_segment_distance(plat, plon, alat, alon, blat, blon):
    lat0 = plat
    px, py = to_local(plat, plon, lat0)
    ax, ay = to_local(alat, alon, lat0)
    bx, by = to_local(blat, blon, lat0)
    dx, dy = bx - ax, by - ay
    if dx == 0 and dy == 0:
        return math.hypot(px - ax, py - ay)
    t = ((px - ax) * dx + (py - ay) * dy) / (dx * dx + dy * dy)
    t = max(0.0, min(1.0, t))
    return math.hypot(px - (ax + t * dx), py - (ay + t * dy))


def circular_mean(degrees, weights):
    """Media circolare pesata. Ritorna (media, lunghezza risultante 0-1)."""
    sx = sy = total = 0.0
    for deg, w in zip(degrees, weights):
        r = math.radians(deg)
        sx += math.cos(r) * w
        sy += math.sin(r) * w
        total += w
    if total == 0:
        return None, 0.0
    sx /= total
    sy /= total
    mean = (math.degrees(math.atan2(sy, sx)) + 360.0) % 360.0
    return mean, math.hypot(sx, sy)


# --------------------------------------------------------------------------- overpass


def overpass(query, attempt=0):
    data = urllib.parse.urlencode({"data": query}).encode()
    endpoint = OVERPASS_ENDPOINTS[attempt % len(OVERPASS_ENDPOINTS)]
    request = urllib.request.Request(
        endpoint, data=data,
        headers={"User-Agent": "CalaGiusta-catalog-builder/1.0 (contatto: tua@email)"},
    )
    try:
        with urllib.request.urlopen(request, timeout=240) as response:
            return json.loads(response.read().decode())
    except (urllib.error.HTTPError, urllib.error.URLError, TimeoutError) as error:
        if attempt >= 4:
            raise
        wait = 20 * (attempt + 1)
        print(f"    ! {error} — riprovo fra {wait}s", file=sys.stderr)
        time.sleep(wait)
        return overpass(query, attempt + 1)


def tile_query(south, west, north, east):
    box = f"{south},{west},{north},{east}"
    return f"""
[out:json][timeout:240];
way["natural"="coastline"]({box});
out geom;
(
  node["natural"="beach"]({box});
  way["natural"="beach"]({box});
  relation["natural"="beach"]({box});
);
out center tags;
node["place"~"^(city|town|village|hamlet)$"]({box});
out tags;
"""


# --------------------------------------------------------------------------- parsing


def parse_tile(payload):
    segments, beaches, places = [], [], []
    for element in payload.get("elements", []):
        tags = element.get("tags", {}) or {}
        if element.get("type") == "way" and tags.get("natural") == "coastline":
            geometry = element.get("geometry") or []
            for i in range(len(geometry) - 1):
                a, b = geometry[i], geometry[i + 1]
                segments.append((a["lat"], a["lon"], b["lat"], b["lon"]))
        elif tags.get("natural") == "beach":
            if "center" in element:
                lat, lon = element["center"]["lat"], element["center"]["lon"]
            elif "lat" in element:
                lat, lon = element["lat"], element["lon"]
            else:
                continue
            beaches.append({
                "osm": f"{element['type']}/{element['id']}",
                "lat": lat, "lon": lon, "tags": tags,
            })
        elif tags.get("place") and "lat" in element:
            places.append((element["lat"], element["lon"], tags.get("name", "")))
    return segments, beaches, places


def analyse(beach, segments):
    """Orientamento e riparo dalla geometria della costa vicina."""
    lat, lon = beach["lat"], beach["lon"]
    bearings, weights, nearest = [], [], 1e9

    for alat, alon, blat, blon in segments:
        # scarto veloce prima del calcolo esatto
        if abs(alat - lat) > 0.02 and abs(blat - lat) > 0.02:
            continue
        if abs(alon - lon) > 0.03 and abs(blon - lon) > 0.03:
            continue
        distance = point_segment_distance(lat, lon, alat, alon, blat, blon)
        if distance > SEARCH_RADIUS_M:
            continue
        nearest = min(nearest, distance)
        length = haversine(alat, alon, blat, blon)
        if length < 1.0:
            continue
        # terra a sinistra, mare a destra => il mare sta a +90 gradi
        sea = (bearing(alat, alon, blat, blon) + 90.0) % 360.0
        bearings.append(sea)
        weights.append(length / (1.0 + distance / 150.0))

    if not bearings:
        return None

    orientation, resultant = circular_mean(bearings, weights)
    if orientation is None:
        return None

    # costa dritta => normali tutte uguali => resultant ~1 => spiaggia aperta
    # cala stretta => normali a ventaglio => resultant basso => molto riparata
    shelter = max(0.0, min(0.9, (1.0 - resultant) * 1.8))
    confidence = resultant if nearest < 400 else resultant * 0.7
    return {
        "orientation": round(orientation, 1),
        "shelter": round(shelter, 2),
        "confidence": round(confidence, 2),
        "coast_distance": round(nearest),
    }


SURFACE_MAP = {
    "sand": "sabbia", "fine_gravel": "ghiaia fine", "gravel": "ghiaia",
    "pebblestone": "ciottoli", "pebbles": "ciottoli", "rock": "roccia",
    "stone": "roccia", "shingle": "ciottoli", "grass": "erba", "mud": "fango",
}


def build_beach(beach, analysis, places):
    tags = beach["tags"]
    name = tags.get("name") or tags.get("name:it")
    if not name:
        return None

    area = ""
    best = 1e9
    for plat, plon, pname in places:
        distance = haversine(beach["lat"], beach["lon"], plat, plon)
        if distance < best and distance < 15000:
            best, area = distance, pname

    labels = []
    if tags.get("sport") and "kitesurf" in tags["sport"]:
        labels.append("kitespot")
    if tags.get("sport") and "surf" in tags["sport"]:
        labels.append("surfspot")
    if tags.get("access") in ("yes", "public", "permissive"):
        labels.append("accesso libero")
    if tags.get("nudism") in ("yes", "designated"):
        labels.append("naturista")
    if tags.get("dog") in ("yes", "leashed"):
        labels.append("cani ammessi")
    if tags.get("blue_flag") == "yes":
        labels.append("bandiera blu")
    if analysis["shelter"] >= 0.5:
        labels.append("cala riparata")

    return {
        "id": beach["osm"].replace("/", "-"),
        "name": name,
        "area": area,
        "latitude": round(beach["lat"], 5),
        "longitude": round(beach["lon"], 5),
        "orientation": analysis["orientation"],
        "shelter": analysis["shelter"],
        "seabed": SURFACE_MAP.get(tags.get("surface", ""), "sabbia"),
        "tags": labels,
        "notes": tags.get("description", "") or tags.get("description:it", ""),
        "confidence": analysis["confidence"],
        "source": "osm",
    }


def dedupe(beaches):
    """Toglie i doppioni: stesso nome entro DEDUPE_M metri."""
    kept = []
    grid = {}
    for beach in sorted(beaches, key=lambda b: -b["confidence"]):
        cell = (int(beach["latitude"] * 1000), int(beach["longitude"] * 1000))
        neighbours = []
        for dy in (-1, 0, 1):
            for dx in (-1, 0, 1):
                neighbours += grid.get((cell[0] + dy, cell[1] + dx), [])
        duplicate = any(
            o["name"].lower() == beach["name"].lower()
            and haversine(beach["latitude"], beach["longitude"], o["latitude"], o["longitude"]) < DEDUPE_M
            for o in neighbours
        )
        if duplicate:
            continue
        grid.setdefault(cell, []).append(beach)
        kept.append(beach)
    return kept


# --------------------------------------------------------------------------- main


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--bbox", nargs=4, type=float, metavar=("S", "W", "N", "E"),
                        default=list(DEFAULT_BBOX))
    parser.add_argument("--out", default="dist")
    parser.add_argument("--base-url", default="https://TUO-UTENTE.github.io/calagiusta-catalog",
                        help="URL pubblico dove verranno serviti i file")
    parser.add_argument("--sleep", type=float, default=4.0)
    arguments = parser.parse_args()

    south, west, north, east = arguments.bbox
    os.makedirs(arguments.out, exist_ok=True)

    collected, tiles = [], []
    lat = south
    while lat < north:
        lon = west
        while lon < east:
            tiles.append((lat, lon, min(lat + TILE_DEG, north), min(lon + TILE_DEG, east)))
            lon += TILE_DEG
        lat += TILE_DEG

    print(f"{len(tiles)} riquadri da interrogare")
    for index, (s, w, n, e) in enumerate(tiles, 1):
        print(f"[{index}/{len(tiles)}] bbox {s:.0f},{w:.0f} → ", end="", flush=True)
        try:
            payload = overpass(tile_query(s, w, n, e))
        except Exception as error:
            print(f"saltato ({error})")
            continue
        segments, beaches, places = parse_tile(payload)
        if not beaches or not segments:
            print(f"{len(beaches)} spiagge, {len(segments)} segmenti di costa — niente da fare")
            time.sleep(arguments.sleep)
            continue

        added = 0
        for beach in beaches:
            analysis = analyse(beach, segments)
            if not analysis or analysis["confidence"] < MIN_CONFIDENCE:
                continue
            record = build_beach(beach, analysis, places)
            if record:
                collected.append(record)
                added += 1
        print(f"{added} spiagge valide su {len(beaches)}")
        time.sleep(arguments.sleep)

    collected = dedupe(collected)
    collected.sort(key=lambda b: (b["area"], b["name"]))

    version = int(time.time())
    catalog = {
        "version": version,
        "generatedAt": datetime.now(timezone.utc).isoformat(timespec="seconds"),
        "count": len(collected),
        "beaches": collected,
    }

    catalog_path = os.path.join(arguments.out, "catalog.json")
    with open(catalog_path, "w", encoding="utf-8") as handle:
        json.dump(catalog, handle, ensure_ascii=False, separators=(",", ":"))

    digest = hashlib.sha256(open(catalog_path, "rb").read()).hexdigest()
    manifest = {
        "version": version,
        "generatedAt": catalog["generatedAt"],
        "count": len(collected),
        "url": f"{arguments.base_url.rstrip('/')}/catalog.json",
        "sha256": digest,
        "minimumAppBuild": 1,
    }
    with open(os.path.join(arguments.out, "manifest.json"), "w", encoding="utf-8") as handle:
        json.dump(manifest, handle, ensure_ascii=False, indent=2)

    size = os.path.getsize(catalog_path) / 1024
    print(f"\n✓ {len(collected)} spiagge · {size:.0f} KB · versione {version}")
    print(f"  {catalog_path}")


if __name__ == "__main__":
    main()
