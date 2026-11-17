"""Read-only finite diagnostic of the exact PatternData.Covered geometry.

No Lean proofs are generated. Normalize only masks unused by Covered/bonds:
X-site masks to empty and U-tip masks to empty. All other masks are enumerated.
"""
import ast
from collections import Counter
from itertools import combinations, product
import json
from pathlib import Path

OUT = Path(__file__).resolve().parent
ORIGIN = (0, 0)
DIRECTIONS = ((1, 0), (0, 1), (-1, 0), (0, -1))
AXIAL = DIRECTIONS
CORNERS = ((1, 1), (-1, 1), (-1, -1), (1, -1))
TIPS = tuple((2*x, 2*y) for x, y in AXIAL)
TEMPLATE = {ORIGIN, *AXIAL, *CORNERS, *TIPS}
EDGES = tuple(sorted((a, b) for a in TEMPLATE for b in TEMPLATE
                     if a < b and abs(a[0]-b[0])+abs(a[1]-b[1]) == 1))
PERIPHERAL_SLOTS = {x: (3 if x in TIPS else 2) for x in (*CORNERS, *TIPS)}
BIT = {d: 1 << i for i, d in enumerate(DIRECTIONS)}


def toward(a, b):
    return BIT[(b[0]-a[0], b[1]-a[1])]


def canonical(outgoing, statuses, bonds):
    def key(reflect):
        def f(x):
            return (-x[0], x[1]) if reflect else x
        return (f(outgoing),
                tuple(sorted((f(x), s) for x, s in statuses.items())),
                tuple(sorted(tuple(sorted((f(a), f(b)))) for a, b in bonds)))
    return min(key(False), key(True))


axial_options = []
for i in range(3):
    center_bit = 1 << ((i+2) % 4)
    axial_options.append([('u', 15), ('x', 0)] +
                         [('d', center_bit | (1 << j))
                          for j in range(4) if (1 << j) != center_bit])
axial_options.append([('x', 0)] + [('d', sum(1 << j for j in js))
                                  for js in combinations((0, 2, 3), 2)])
corner_options = [('u', 15), ('x', 0)] + [
    ('d', sum(1 << j for j in js)) for js in combinations(range(4), 2)]

counts = Counter()
keys = set()
max_erased_degree = 0
max_original_degree = 0
for axial_values in product(*axial_options):
    axial_data = dict(zip(AXIAL, axial_values))
    allowed_corners = []
    for corner in CORNERS:
        adjacent = [x for x in AXIAL if abs(x[0]-corner[0])+abs(x[1]-corner[1]) == 1]
        allowed = []
        for status, mask in corner_options:
            if all(status == 'x' or axial_data[x][0] == 'x' or
                   bool(mask & toward(corner, x)) ==
                   bool(axial_data[x][1] & toward(x, corner)) for x in adjacent):
                allowed.append((status, mask))
        allowed_corners.append(allowed)
    for corner_values in product(*allowed_corners):
        data = {ORIGIN: ('u', 7), **axial_data,
                **dict(zip(CORNERS, corner_values)),
                **{tip: ('u', 0) for tip in TIPS}}
        bonds = tuple((a, b) for a, b in EDGES
                      if data[a][0] != 'x' and data[b][0] != 'x'
                      and (a in TIPS or data[a][1] & toward(a, b))
                      and (b in TIPS or data[b][1] & toward(b, a)))
        counts['consistent_configurations'] += 1
        degree = Counter(x for e in bonds for x in e)
        incident = {b if a == ORIGIN else a for a, b in bonds if ORIGIN in (a, b)}
        expected_incident = {x for x in AXIAL[:3] if data[x][0] != 'x'}
        assert incident == expected_incident
        erased_degree = Counter(x for e in bonds if ORIGIN not in e for x in e)
        for x in TEMPLATE:
            if data[x][0] == 'x':
                assert degree[x] == 0
                continue
            slots = PERIPHERAL_SLOTS.get(x, 0)
            assert degree[x] + slots <= 4
            max_original_degree = max(max_original_degree, degree[x] + slots)
            if x != ORIGIN:
                assert erased_degree[x] + slots <= 4
                max_erased_degree = max(max_erased_degree, erased_degree[x] + slots)
        effective_status = {x: data[x][0] for x in (*AXIAL, *CORNERS) if degree[x]}
        for outgoing in expected_incident:
            counts['marked_patterns'] += 1
            if outgoing in AXIAL[:2]:
                counts['marked_north_or_east'] += 1
            keys.add(canonical(outgoing, effective_status, bonds))

source = json.loads(Path('/home/ubuntu/aklt/data/h1/inputs/pext7962.json').read_text())
source_keys = set()
for p in source:
    bonds = tuple(tuple(tuple(x) for x in e) for e in p['present'])
    degree = Counter(x for e in bonds for x in e)
    statuses = {ast.literal_eval(x): s for x, s in p['kinds'].items()
                if degree[ast.literal_eval(x)] and s != 'x'}
    source_keys.add(canonical(tuple(p['out']), statuses, bonds))
assert keys == source_keys
assert len(source_keys) == len(source) == 7962
assert counts == {'consistent_configurations': 106101,
                  'marked_patterns': 184914, 'marked_north_or_east': 123339}
result = dict(counts, canonical_keys=len(keys), missing_keys=len(keys-source_keys),
              extra_keys=len(source_keys-keys), max_original_factors=max_original_degree,
              max_erased_factors=max_erased_degree, passage_bonds='PASS', result='PASS')
(OUT/'geometry-check.json').write_text(json.dumps(result, indent=2, sort_keys=True)+'\n')
print(json.dumps(result, sort_keys=True))
