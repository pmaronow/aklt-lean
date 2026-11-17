"""Independent integer decoding and trail reconstruction for FID_T159.

Reads only the supplied Lean source; does not import its trail predicates.
"""
from pathlib import Path
import ast
from collections import Counter
import hashlib
import json
import re

BASE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs')
source = (BASE / 'Automaton10Data.lean').read_text()
literals = {
    m[1]: int(m[2], 16)
    for m in re.finditer(r'private noncomputable def (\w+) : ℕ := (0x[0-9a-f]+)', source)
}


def flatten(node, shift=0):
    if isinstance(node, ast.Name):
        return [(node.id, shift)]
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add):
        return flatten(node.left, shift) + flatten(node.right, shift)
    if (isinstance(node, ast.BinOp) and isinstance(node.op, ast.LShift)
            and isinstance(node.right, ast.Constant)):
        return flatten(node.left, shift + node.right.value)
    raise ValueError(ast.dump(node))


parts = {}
tables = {}
for name, width, length in [('rawClass', 12, 4**10), ('representatives', 20, 3741),
                            ('destinations', 12, 4*3741), ('edgeKinds', 2, 4*3741)]:
    expression = re.search(r'^noncomputable def ' + name + r' : ℕ := (.+)$', source, re.M)[1]
    leaves = flatten(ast.parse(expression.replace('<<<', '<<'), mode='eval').body)
    assert len({n for n, _ in leaves}) == len(leaves)
    leaves.sort(key=lambda x: x[1])
    for (n, offset), (_, following) in zip(leaves, leaves[1:]):
        assert literals[n] < 2**(following-offset), n
    packed = sum(literals[n] << offset for n, offset in leaves)
    assert packed < 2**(width*length)
    parts[name] = leaves
    # Read lanes from a byte stream rather than repeatedly shifting a huge int.
    stream = packed.to_bytes((width*length+7)//8, 'little')
    lanes = []
    for i in range(length):
        bit = width*i
        start = bit//8
        bytecount = (bit%8+width+7)//8
        lanes.append((int.from_bytes(stream[start:start+bytecount], 'little') >> (bit%8)) & (2**width-1))
    tables[name] = lanes

classes, representatives, destinations, kinds = [tables[n] for n in
    ['rawClass', 'representatives', 'destinations', 'edgeKinds']]
STEPS = [(1, 0), (0, 1), (-1, 0), (0, -1)]
raw = {}
depth_counts = Counter()


def extend(code, vertices, bonds, directions):
    length = len(directions)
    depth_counts[length] += 1
    if length == 10:
        end = vertices[-1]
        revisit = end in vertices[:-1]
        allowed = []
        detected = []
        for d, (dx, dy) in enumerate(STEPS):
            nxt = (end[0]+dx, end[1]+dy)
            allowed.append(frozenset((end, nxt)) not in bonds and d != (directions[-1]+2)%4)
            detected.append(2 if revisit else (0 if d == directions[-1] else 1))
        raw[code] = (tuple(allowed), tuple(detected), directions[-1])
        return
    end = vertices[-1]
    for d, (dx, dy) in enumerate(STEPS):
        nxt = (end[0]+dx, end[1]+dy)
        bond = frozenset((end, nxt))
        if bond not in bonds:
            extend(4*code+d, vertices+[nxt], bonds | {bond}, directions+[d])


extend(0, [(0, 0)], set(), [])
errors = []
for code, c in enumerate(classes):
    if not (c <= 3741 and (c < 3741) == (code in raw)):
        errors.append(('coverage', code, c))
for c, code in enumerate(representatives):
    if not (code < 4**10 and code in raw and classes[code] == c):
        errors.append(('representative', c, code))
for i, (dest, kind) in enumerate(zip(destinations, kinds)):
    if not (dest <= 3741 and (dest == 0) == (kind == 3) and (dest == 0 or kind < 3)):
        errors.append(('edge-range', i, dest, kind))
comparisons = Counter()
for code, (allow, detected, arrival) in raw.items():
    c = classes[code]
    repallow, repkind, reparrival = raw[representatives[c]]
    for d in range(4):
        comparisons['raw_directions'] += 1
        if allow[d] != repallow[d] or detected[d] != repkind[d]:
            errors.append(('representative-behavior', code, c, d))
        i = 4*c+d
        if allow[d] != (destinations[i] != 0):
            errors.append(('stored-admissibility', code, c, d))
        if allow[d]:
            comparisons['admissible_successors'] += 1
            successor = (4*code+d) % (4**10)
            if kinds[i] != detected[d] or destinations[i] != classes[successor]+1:
                errors.append(('stored-kind-successor', code, c, d))
            if detected[d] != 2:
                comparisons['nonrevisit_arrivals'] += 1
                if arrival != reparrival:
                    errors.append(('arrival', code, c, d))

target_results = []
offsets = dict(parts['rawClass'])
for k in range(760, 765):
    name = f'rawClass_{k}'
    offset = offsets[name]
    lo, hi = offset//12, (offset+16384-1)//12
    affected = range(lo, hi+1)
    valid = [code for code in affected if code in raw]
    target_results.append(dict(
        declaration=name,
        line=next(i for i, line in enumerate(source.splitlines(), 1)
                  if line.startswith(f'private noncomputable def {name} ')),
        offset=offset, width=16384, first_code=lo, last_code=hi,
        valid=len(valid), invalid=(hi-lo+1)-len(valid),
        sentinel=sum(classes[code] == 3741 for code in affected),
        classes=len({classes[code] for code in valid}),
        literal_sha256=hashlib.sha256(literals[name].to_bytes(2048, 'big')).hexdigest(),
        examples=[dict(code=code, word=''.join('ENWS'[(code >> shift)&3]
                      for shift in range(18, -1, -2)),
                      quotient=classes[code], representative=representatives[classes[code]])
                  for code in valid[:3]],
    ))

result = dict(
    targets=target_results,
    raw_counts={j: depth_counts[j] for j in range(1, 11)},
    distinct_classes=len({classes[code] for code in raw}),
    edge_counts=dict(Counter(k for dest, k in zip(destinations, kinds) if dest != 0)),
    comparisons=dict(comparisons), errors_count=len(errors), errors=errors[:20],
)
print(json.dumps(result, indent=2))
assert not errors
assert result['edge_counts'] == {0: 2516, 1: 5032, 2: 1872}
