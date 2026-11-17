"""Independent finite reconstruction of the Lean literals and paper trail rules.

Reads only the designated Lean source; does not use an archived automaton.
"""

import ast
from collections import Counter
from pathlib import Path
import re

SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
source = SOURCE.read_text()
values = {}
trees = {}
for line in source.splitlines():
    match = re.fullmatch(r'(?:private )?noncomputable def (\w+) : ℕ := (.+)', line)
    if not match:
        continue
    name, expression = match.groups()
    tree = ast.parse(expression.replace('<<<', '<<'), mode='eval').body
    trees[name] = tree

    def evaluate(node):
        if isinstance(node, ast.Constant) and type(node.value) is int:
            return node.value
        if isinstance(node, ast.Name):
            return values[node.id]
        if isinstance(node, ast.BinOp):
            left, right = evaluate(node.left), evaluate(node.right)
            if isinstance(node.op, ast.Add):
                return left + right
            if isinstance(node.op, ast.LShift):
                return left << right
        raise ValueError(ast.dump(node))

    values[name] = evaluate(tree)


def summands(node, shift=0):
    if isinstance(node, ast.Name):
        return [(node.id, shift)]
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add):
        return summands(node.left, shift) + summands(node.right, shift)
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.LShift):
        assert isinstance(node.right, ast.Constant)
        return summands(node.left, shift + node.right.value)
    raise ValueError(ast.dump(node))


offsets = dict(summands(trees['rawClass']))
assert len(offsets) == 768
assert all(offsets[f'rawClass_{i}'] == max(0, (767 - i) * 16384 - 4) for i in range(768))
assert all(values[f'rawClass_{i}'] < 2**16384 for i in range(767))
assert values['rawClass_767'] < 2**16380
assert values['rawClass'] == sum(values[n] << offset for n, offset in offsets.items())
print('All raw chunks are disjoint consecutive blocks in descending order: 767 x 16384 bits, then 16380 bits; four leading zero bits are implicit.')

packed = values['rawClass'].to_bytes(12 * 4**10 // 8, 'little')
classes = []
for offset in range(0, len(packed), 3):
    v = int.from_bytes(packed[offset:offset+3], 'little')
    classes.extend((v & 4095, v >> 12))
assert len(classes) == 4**10


def lane(name, width, index):
    return (values[name] >> (width * index)) & ((1 << width) - 1)


def decode(code):
    return tuple((code >> (2 * i)) & 3 for i in range(9, -1, -1))


STEPS = ((1, 0), (0, 1), (-1, 0), (0, -1))


def add(v, d):
    dx, dy = STEPS[d]
    return (v[0] + dx, v[1] + dy)


def bond(a, b):
    return frozenset((a, b))


def model(word):
    vertices = [(0, 0)]
    bonds = set()
    for d in word:
        endpoint = add(vertices[-1], d)
        edge = bond(vertices[-1], endpoint)
        if edge in bonds:
            return None
        bonds.add(edge)
        vertices.append(endpoint)
    return vertices, bonds


representatives = [lane('representatives', 20, a) for a in range(3741)]
destinations = [[lane('destinations', 12, 4*a+d) for d in range(4)] for a in range(3741)]
kinds = [[lane('edgeKinds', 2, 4*a+d) for d in range(4)] for a in range(3741)]
errors = Counter()
examples = {}


def check(condition, label, info):
    if not condition:
        errors[label] += 1
        examples.setdefault(label, info)


for a, code in enumerate(representatives):
    check(code < 4**10, 'representative code range', (a, code))
    check(model(decode(code)) is not None, 'representative raw', (a, code))
    check(classes[code] == a, 'representative maps to own class', (a, code, classes[code]))
    for d in range(4):
        dest, kind = destinations[a][d], kinds[a][d]
        check(0 <= dest <= 3741, 'destination range', (a, d, dest))
        check((dest == 0) == (kind == 3), 'invalid edge sentinel', (a, d, dest, kind))

target_bits = {i: (offsets[f'rawClass_{i}'], offsets[f'rawClass_{i}'] + 16383) for i in range(240, 245)}
target_codes = {
    i: range(low // 12, high // 12 + 1)
    for i, (low, high) in target_bits.items()
}
target_union = set().union(*(set(r) for r in target_codes.values()))
target_raw = Counter()
target_class_sets = {i: set() for i in target_codes}
raw_codes = set()
raw_counts = Counter()
class_signatures = {}


def visit(word, code, vertices, bonds):
    raw_counts[len(word)] += 1
    if len(word) == 10:
        raw_codes.add(code)
        a = classes[code]
        check(a < 3741, 'raw word assigned sentinel/out of range', (code, a))
        if a >= 3741:
            return
        revisit = vertices[-1] in vertices[:-1]
        signature = []
        for d in range(4):
            admissible = d != (word[-1] + 2) % 4 and bond(vertices[-1], add(vertices[-1], d)) not in bonds
            kind = 2 if revisit else (0 if d == word[-1] else 1)
            successor_code = (code % 4**9) * 4 + d
            successor_class = classes[successor_code]
            signature.append((admissible, kind, successor_class if admissible else None))
            check((destinations[a][d] != 0) == admissible, 'admissibility', (code, a, d))
            if admissible:
                check(kinds[a][d] == kind, 'kind', (code, a, d, kind, kinds[a][d]))
                check(destinations[a][d] - 1 == successor_class, 'successor', (code, a, d, successor_class, destinations[a][d]))
                if kind != 2:
                    check(representatives[a] % 4 == word[-1], 'nonrevisit arrival', (code, a, d))
        signature = tuple(signature), word[-1] if any(x[0] and x[1] != 2 for x in signature) else None
        if a in class_signatures:
            check(signature == class_signatures[a], 'class projection compatibility', (code, a))
        else:
            class_signatures[a] = signature
        if code in target_union:
            for i, codes in target_codes.items():
                if code in codes:
                    target_raw[i] += 1
                    target_class_sets[i].add(a)
        return
    for d in range(4):
        endpoint = add(vertices[-1], d)
        edge = bond(vertices[-1], endpoint)
        if edge not in bonds:
            visit(word + (d,), code * 4 + d, vertices + (endpoint,), bonds | {edge})


visit((), 0, ((0, 0),), set())
print('Independent raw-window counts by length:', dict(sorted(raw_counts.items())))
for code, a in enumerate(classes):
    check(a <= 3741, 'raw class range', (code, a))
    check((a < 3741) == (code in raw_codes), 'coverage equivalence', (code, a, code in raw_codes))
print('Classes attained by raw words:', len(class_signatures))
print('Packed quotient admitted edge kinds:', dict(Counter(kinds[a][d] for a in range(3741) for d in range(4) if destinations[a][d] != 0)))
for i, codes in target_codes.items():
    low, high = target_bits[i]
    histogram = Counter(classes[c] for c in codes)
    invalid = len(codes) - target_raw[i]
    print(f'rawClass_{i}: bits [{low},{high}], overlapping codes [{codes.start},{codes.stop-1}], '
          f'{len(codes)} lanes; raw={target_raw[i]}, nonraw={invalid}, classes={len(target_class_sets[i])}; '
          f'first/last lane={classes[codes.start]}/{classes[codes.stop-1]}; '
          f'boundary bit offsets={low%12}/{(high+1)%12}; '
          f'nonraw sentinel count={histogram[3741]}')
print('ERROR COUNTS:', dict(errors))
print('FIRST ERROR EXAMPLES:', examples)
assert not errors
