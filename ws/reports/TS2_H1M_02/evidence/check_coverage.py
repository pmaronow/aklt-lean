#!/usr/bin/env python3
"""Independent finite translation of PatternData.Covered and .bonds.

Only kept decisions ignored by those definitions are quotiented out: kept sets
at tips and X sites. No historical pattern enumerator is imported.
"""
import ast
import itertools
import json
from pathlib import Path
import time

BASE = Path('/home/ubuntu/aklt/data/h1')
HERE = Path(__file__).resolve().parent
DIRECTIONS = ((1, 0), (0, 1), (-1, 0), (0, -1))
CENTER = (0, 0)
ARRIVAL = (0, -1)
NEIGHBORS = DIRECTIONS[:3]
TIPS = ((2, 0), (0, 2), (-2, 0), (0, -2))
CORNERS = ((1, 1), (-1, 1), (-1, -1), (1, -1))
RING = ((1, 0), (1, 1), (0, 1), (-1, 1), (-1, 0), (-1, -1), (0, -1), (1, -1))
SITES = tuple((x, y) for x in range(-2, 3) for y in range(-2, 3) if abs(x)+abs(y) <= 2)
NON_TIPS = tuple(x for x in SITES if x not in TIPS)


def add(x, y):
    return (x[0]+y[0], x[1]+y[1])


def neighbors(x):
    return frozenset(add(x, d) for d in DIRECTIONS)


def edge(x, y):
    return tuple(sorted((x, y)))


EDGES = tuple(edge(x, y) for x in SITES for y in SITES if x < y and sum(abs(x[k]-y[k]) for k in (0, 1)) == 1)
NON_TIP_EDGES = tuple((x, y) for x, y in EDGES if x not in TIPS and y not in TIPS)
ALL_KEPT = {x: neighbors(x) for x in SITES}


def options(x):
    ns = ALL_KEPT[x]
    if x == ARRIVAL:
        return [('x', frozenset())] + [('d', frozenset(k)) for k in itertools.combinations(sorted(ns-{CENTER}), 2)]
    if x in NEIGHBORS:
        return [('u', ns), ('x', frozenset())] + [('d', frozenset((CENTER, y))) for y in sorted(ns-{CENTER})]
    assert x in CORNERS
    return [('u', ns), ('x', frozenset())] + [('d', frozenset(k)) for k in itertools.combinations(sorted(ns), 2)]


def key(kinds, bonds, out, reflect=False):
    def tx(x):
        return (-x[0], x[1]) if reflect else x
    incident = {x for b in bonds for x in b}
    active_kinds = tuple(sorted((tx(x), kinds[x]) for x in RING if x in incident))
    return tx(out), active_kinds, tuple(sorted(edge(tx(x), tx(y)) for x, y in bonds))


def canonical(kinds, bonds, out):
    return min(key(kinds, bonds, out), key(kinds, bonds, out, True))


def main():
    started = time.monotonic()
    records = json.loads((BASE/'inputs/pext7962.json').read_text())
    supplied = set()
    for p in records:
        kinds = {ast.literal_eval(x): s for x, s in p['kinds'].items()}
        bonds = tuple(edge(tuple(a), tuple(b)) for a, b in p['present'])
        supplied.add(canonical(kinds, bonds, tuple(p['out'])))
    assert len(supplied) == len(records) == 7962

    order = (ARRIVAL,) + NEIGHBORS + CORNERS
    counts = dict(assignments=0, consistent=0, marked_all=0, marked_north_east=0)
    obtained = set()
    fixed = {CENTER: ('u', frozenset(NEIGHBORS)), **{x: ('u', frozenset()) for x in TIPS}}
    for choices in itertools.product(*(options(x) for x in order)):
        counts['assignments'] += 1
        data = dict(zip(order, choices)) | fixed
        if any(data[x][0] != 'x' and data[y][0] != 'x' and ((y in data[x][1]) != (x in data[y][1])) for x, y in NON_TIP_EDGES):
            continue
        counts['consistent'] += 1
        bonds = tuple((x, y) for x, y in EDGES if data[x][0] != 'x' and data[y][0] != 'x' and (x in TIPS or y in data[x][1]) and (y in TIPS or x in data[y][1]))
        kinds = {x: s for x, (s, _) in data.items()}
        for out in NEIGHBORS:
            if kinds[out] == 'x':
                continue
            counts['marked_all'] += 1
            if out in DIRECTIONS[:2]:
                counts['marked_north_east'] += 1
            obtained.add(canonical(kinds, bonds, out))

    result = dict(result='PASS', **counts, effective_keys=len(obtained), supplied_keys=len(supplied),
                  missing=len(obtained-supplied), extra=len(supplied-obtained),
                  elapsed_seconds=time.monotonic()-started)
    assert tuple(counts.values()) == (2048000, 106101, 184914, 123339), result
    assert obtained == supplied, result
    (HERE/'coverage.json').write_text(json.dumps(result, indent=2, sort_keys=True)+'\n')
    print(json.dumps(result, sort_keys=True), flush=True)


if __name__ == '__main__':
    main()
