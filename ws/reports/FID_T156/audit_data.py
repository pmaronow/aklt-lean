"""Read-only arithmetic audit of the supplied Lean automaton literals.

Uses the actual parenthesized shift/add expressions, then independently
enumerates square-lattice trails. No archived generator or witness is read.
"""

import ast
from collections import Counter
from pathlib import Path
import re


SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
TEXT = SOURCE.read_text()
LITERALS = {
    name: int(value, 16)
    for name, value in re.findall(
        r'private noncomputable def (\w+) : ℕ := 0x([0-9a-f]+)', TEXT
    )
}


def unpack(name, width, count):
    expression = re.search(
        r'^noncomputable def ' + name + r' : ℕ := (.+)$', TEXT, re.M
    )[1].replace('<<<', '<<')

    def evaluate(node, offset=0):
        if isinstance(node, ast.Name):
            return LITERALS[node.id] << offset, [(node.id, offset)]
        if isinstance(node, ast.BinOp) and isinstance(node.op, ast.LShift):
            assert isinstance(node.right, ast.Constant)
            return evaluate(node.left, offset + node.right.value)
        if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add):
            left, left_parts = evaluate(node.left, offset)
            right, right_parts = evaluate(node.right, offset)
            return left + right, left_parts + right_parts
        raise ValueError(ast.dump(node))

    packed, parts = evaluate(ast.parse(expression, mode='eval').body)
    assert packed < 1 << (width * count)
    assert len(parts) == len(set(n for n, _ in parts))
    for (high_name, high), (low_name, low) in zip(parts, parts[1:]):
        assert high > low
        assert LITERALS[low_name] < 1 << (high - low)
    lanes = []
    accumulator = bits = 0
    for byte in packed.to_bytes((width * count + 7) // 8, 'little'):
        accumulator |= byte << bits
        bits += 8
        while bits >= width and len(lanes) < count:
            lanes.append(accumulator & ((1 << width) - 1))
            accumulator >>= width
            bits -= width
    assert len(lanes) == count
    print(name, 'parts:', len(parts), 'lanes:', count, 'max:', max(lanes))
    return lanes, parts


classes, class_parts = unpack('rawClass', 12, 4**10)
representatives, _ = unpack('representatives', 20, 3741)
destinations, _ = unpack('destinations', 12, 3741 * 4)
kinds, _ = unpack('edgeKinds', 2, 3741 * 4)

STEPS = ((1, 0), (0, 1), (-1, 0), (0, -1))
raw = {}
depth_counts = [0] * 11


def bond(u, v):
    return tuple(sorted((u, v)))


def generate(word=(), vertices=((0, 0),), bonds=frozenset(), code=0):
    depth_counts[len(word)] += 1
    if len(word) == 10:
        assert code not in raw
        raw[code] = (word, vertices, bonds)
        return
    x, y = vertices[-1]
    for d, (dx, dy) in enumerate(STEPS):
        endpoint = (x + dx, y + dy)
        edge = bond((x, y), endpoint)
        if edge not in bonds:
            generate(word + (d,), vertices + (endpoint,), bonds | {edge}, code * 4 + d)


generate()
assert depth_counts[1:] == [4, 12, 36, 108, 316, 916, 2628, 7500, 21268, 60092]
coverage_errors = [c for c, a in enumerate(classes) if a > 3741 or ((a < 3741) != (c in raw))]
assert not coverage_errors, coverage_errors[:5]
assert len({classes[c] for c in raw}) == 3741
for a, code in enumerate(representatives):
    assert code < 4**10 and code in raw and classes[code] == a
for destination, kind in zip(destinations, kinds):
    assert 0 <= destination <= 3741
    assert (destination == 0) == (kind == 3)
    assert destination == 0 or kind < 3


def transition(state, d):
    word, vertices, bonds = state
    x, y = vertices[-1]
    dx, dy = STEPS[d]
    admissible = d != (word[-1] + 2) % 4 and bond((x, y), (x + dx, y + dy)) not in bonds
    kind = 2 if vertices[-1] in vertices[:-1] else (0 if d == word[-1] else 1)
    return admissible, kind


for code, state in raw.items():
    a = classes[code]
    representative = raw[representatives[a]]
    for d in range(4):
        admissible, kind = transition(state, d)
        rep_admissible, rep_kind = transition(representative, d)
        assert (admissible, kind) == (rep_admissible, rep_kind), (code, a, d)
        index = 4 * a + d
        assert admissible == (destinations[index] != 0), (code, a, d)
        if admissible:
            successor_code = (code % 4**9) * 4 + d
            assert successor_code in raw
            assert kinds[index] == kind, (code, a, d, 'kind')
            assert destinations[index] - 1 == classes[successor_code], (code, a, d, 'successor')
            if kind != 2:
                assert state[0][-1] == representatives[a] % 4, (code, a, d, 'arrival')

edge_counts = Counter(k for destination, k in zip(destinations, kinds) if destination)
assert edge_counts == {0: 2516, 1: 5032, 2: 1872}
print('depth counts:', depth_counts[1:])
print('raw coverage and sentinel checks: PASS (all 1048576 codes)')
print('representative checks: PASS (all 3741 classes)')
print('quotient checks: PASS (all 60092 raw words, all four absolute directions)')
print('edge counts:', dict(sorted(edge_counts.items())))

for name, offset in class_parts:
    number = int(name.split('_')[-1])
    if 745 <= number <= 749:
        first = offset // 12
        last = (offset + 16384 - 1) // 12
        selected = [c for c in range(first, last + 1) if c in raw]
        histogram = Counter(classes[first:last + 1])
        print(name, 'offset:', offset, 'intersected codes:', (first, last),
              'raw:', len(selected), 'invalid:', histogram[3741],
              'distinct classes:', len({classes[c] for c in selected}),
              'first raw:', (selected[0], classes[selected[0]]) if selected else None)

print('ALL CHECKS PASSED')
