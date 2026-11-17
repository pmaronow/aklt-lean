"""Read-only reconstruction of the supplied Lean automaton data and paper contract."""
from pathlib import Path
import ast
from collections import Counter
import hashlib
import json
import re

SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
text = SOURCE.read_text()
literals = {}
expressions = {}
for line in text.splitlines():
    match = re.fullmatch(r'(?:private )?noncomputable def (\w+) : ℕ := (.*)', line)
    if match:
        name, value = match.groups()
        if re.fullmatch(r'0x[0-9a-f]+', value):
            literals[name] = value[2:]
        else:
            expressions[name] = value

def terms(node, offset=0):
    if isinstance(node, ast.Name):
        assert node.id in literals
        return [(offset, node.id)]
    assert isinstance(node, ast.BinOp)
    if isinstance(node.op, ast.Add):
        return terms(node.left, offset) + terms(node.right, offset)
    assert isinstance(node.op, ast.LShift) and isinstance(node.right, ast.Constant)
    assert isinstance(node.right.value, int) and node.right.value >= 0
    return terms(node.left, offset + node.right.value)

tables = {}
offsets = {}
for name, expr in expressions.items():
    ts = sorted(terms(ast.parse(expr.replace('<<<', '<<'), mode='eval').body))
    assert len({n for _, n in ts}) == len(ts)
    size = 0
    for offset, chunk in ts:
        assert offset == size, (name, offset, size)
        offsets[chunk] = (offset, offset + 4 * len(literals[chunk]) - 1)
        size += 4 * len(literals[chunk])
    tables[name] = ''.join(literals[n] for _, n in reversed(ts))
    print('PACKING', name, 'chunks', len(ts), 'bits', size)
assert set(literals) == set(offsets), 'Unexpected unused literal'
assert len(tables['rawClass']) * 4 <= 12 * 4**10
# Natural numerals omit leading zero nibbles; these belong to the top lane.
tables['rawClass'] = tables['rawClass'].zfill(3 * 4**10)
assert len(tables['representatives']) * 4 == 20 * 3741
assert len(tables['destinations']) * 4 <= 12 * 3741 * 4
tables['destinations'] = tables['destinations'].zfill(3 * 3741 * 4)
assert len(tables['edgeKinds']) * 4 == 2 * 3741 * 4

def unpack(name, width):
    data = tables[name]
    if width % 4 == 0:
        digits = width // 4
        return [int(data[max(0, end-digits):end], 16)
                for end in range(len(data), 0, -digits)]
    assert width == 2
    return [lane for c in reversed(data) for lane in (int(c,16)&3, int(c,16)>>2)]

classes = unpack('rawClass', 12)
reps = unpack('representatives', 20)
destinations = unpack('destinations', 12)
kinds = unpack('edgeKinds', 2)
assert len(classes) == 4**10 and len(reps) == 3741
assert len(destinations) == len(kinds) == 3741 * 4
assert max(classes) <= 3741
assert max(reps) < 4**10 and max(destinations) <= 3741
assert all((dest == 0) == (kind == 3) for dest, kind in zip(destinations, kinds))
assert all(dest == 0 or kind < 3 for dest, kind in zip(destinations, kinds))

STEPS = ((1,0),(0,1),(-1,0),(0,-1))
LABELS = 'ENWS'
def directions(code):
    return tuple((code >> (2*i)) & 3 for i in range(9,-1,-1))

def word_info(ds):
    pos = (0,0)
    departures = []
    bonds = set()
    for d in ds:
        departures.append(pos)
        dx,dy = STEPS[d]
        nxt = (pos[0]+dx,pos[1]+dy)
        bond = tuple(sorted((pos,nxt)))
        assert bond not in bonds
        bonds.add(bond)
        pos = nxt
    allowed = []
    detected_kinds = []
    for d,(dx,dy) in enumerate(STEPS):
        bond = tuple(sorted((pos,(pos[0]+dx,pos[1]+dy))))
        allowed.append(d != (ds[-1]+2)%4 and bond not in bonds)
        detected_kinds.append(2 if pos in departures else (0 if d == ds[-1] else 1))
    return tuple(allowed), tuple(detected_kinds), ds[-1]

raw_codes = []
depth_counts = [0]*11
def generate(depth=0, code=0, pos=(0,0), bonds=None):
    if bonds is None:
        bonds = set()
    depth_counts[depth] += 1
    if depth == 10:
        raw_codes.append(code)
        return
    for d,(dx,dy) in enumerate(STEPS):
        nxt = (pos[0]+dx,pos[1]+dy)
        bond = tuple(sorted((pos,nxt)))
        if bond not in bonds:
            bonds.add(bond)
            generate(depth+1,code*4+d,nxt,bonds)
            bonds.remove(bond)
generate()
assert depth_counts == [1,4,12,36,108,316,916,2628,7500,21268,60092]
assert raw_codes == sorted(set(raw_codes))
assert [code for code,c in enumerate(classes) if c < 3741] == raw_codes
assert set(classes[code] for code in raw_codes) == set(range(3741))
rep_info = []
for a,code in enumerate(reps):
    assert classes[code] == a
    rep_info.append(word_info(directions(code)))

for code in raw_codes:
    a = classes[code]
    ds = directions(code)
    allowed, detected_kinds, arrival = word_info(ds)
    rallowed, rkinds, rarrival = rep_info[a]
    assert allowed == rallowed, ('admissibility', code, a)
    assert detected_kinds == rkinds, ('all-direction kind', code, a)
    for d in range(4):
        dest, kind = destinations[4*a+d], kinds[4*a+d]
        assert (dest != 0) == allowed[d], ('stored admissibility',code,a,d)
        if allowed[d]:
            assert kind == detected_kinds[d], ('stored kind',code,a,d)
            successor = (code % 4**9) * 4 + d
            assert classes[successor] < 3741
            assert dest-1 == classes[successor], ('successor',code,a,d)
            if kind != 2:
                assert arrival == rarrival, ('arrival',code,a,d)

edge_counts = Counter(kind for dest,kind in zip(destinations,kinds) if dest)
assert edge_counts == {0:2516,1:5032,2:1872}
print('RAW_DEPTH_COUNTS', depth_counts)
print('RAW_COVERAGE',len(raw_codes),'SURJECTIVE_CLASSES',len(set(classes[c] for c in raw_codes)))
print('ALL_REPRESENTATIVE_AND_TRANSITION_CHECKS_PASS',len(raw_codes)*4)
print('EDGE_COUNTS',dict(sorted(edge_counts.items())))

target_data = []
for i in range(475,480):
    name = f'rawClass_{i}'
    lo,hi = offsets[name]
    first,last = lo//12,hi//12
    codes = list(range(first,last+1))
    # All touched lanes are outside Omega_10 for a direct, local reason:
    # NW E reverses the second bond; the sole preceding boundary word is NN S^8.
    assert all(c == 393215 or directions(c)[:3] == (1,2,0) for c in codes)
    if 393215 in codes:
        assert directions(393215) == (1,1,3,3,3,3,3,3,3,3)
    assert all(classes[c] == 3741 for c in codes)
    repeating_markers = sum(3741 << (12*j) for j in range(last-first+1))
    expected_chunk = (repeating_markers >> (lo % 12)) & ((1 << (hi-lo+1))-1)
    assert int(literals[name],16) == expected_chunk
    valid = [c for c in codes if classes[c] < 3741]
    interior = [c for c in codes if 12*c >= lo and 12*c+11 <= hi]
    partial = [c for c in codes if c not in interior]
    info = {
        'declaration':name, 'source_line':next(j for j,line in enumerate(text.splitlines(),1) if line.startswith(f'private noncomputable def {name} ')),
        'hex_digits':len(literals[name]),'sha256_hex_ascii':hashlib.sha256(literals[name].encode()).hexdigest(),
        'bit_interval_inclusive':[lo,hi], 'code_interval_inclusive':[first,last],
        'complete_lanes':len(interior),'partial_lanes':partial,'raw_lanes':len(valid),'invalid_lanes':len(codes)-len(valid),
        'distinct_classes':len({classes[c] for c in valid}),
        'first_raw_example':({'code':valid[0],'word':''.join(LABELS[d] for d in directions(valid[0])),'class':classes[valid[0]],'representative':reps[classes[valid[0]]]} if valid else None),
        'partial_lane_values':{str(c):classes[c] for c in partial},
    }
    target_data.append(info)
    print('TARGET',json.dumps(info,sort_keys=True))
Path('/home/ubuntu/aklt/reports/FID_T102/check_results.json').write_text(json.dumps(target_data,indent=2)+'\n')
print('PASS')
