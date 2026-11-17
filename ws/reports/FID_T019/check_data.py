"""Independent reconstruction of the paper's memory-ten finite contract.

Reads only the supplied Lean data file. No archived executable or data file is used.
"""

import ast
from collections import Counter
from hashlib import sha256
from pathlib import Path
import re


SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
text = SOURCE.read_text()
literals = {
    name: int(value, 16)
    for name, value in re.findall(
        r'private noncomputable def (\w+) : ℕ := 0x([0-9a-f]+)', text
    )
}


def expression(name):
    source = re.search(
        rf'^noncomputable def {name} : ℕ := (.+)$', text, re.M
    ).group(1)
    return ast.parse(source.replace('<<<', '<<'), mode='eval').body


def evaluate(node):
    if isinstance(node, ast.Name):
        return literals[node.id]
    if isinstance(node, ast.Constant) and isinstance(node.value, int):
        return node.value
    assert isinstance(node, ast.BinOp)
    if isinstance(node.op, ast.Add):
        return evaluate(node.left) + evaluate(node.right)
    assert isinstance(node.op, ast.LShift)
    # In every shift in the actual file, the shift amount is parenthesized
    # or is an isolated numeric literal; no precedence assumption is needed.
    assert isinstance(node.right, ast.Constant)
    return evaluate(node.left) << node.right.value


def positions(node, offset=0):
    if isinstance(node, ast.Name):
        return [(node.id, offset)]
    assert isinstance(node, ast.BinOp)
    if isinstance(node.op, ast.Add):
        return positions(node.left, offset) + positions(node.right, offset)
    assert isinstance(node.op, ast.LShift)
    return positions(node.left, offset + node.right.value)


def unpack(name, width, length):
    node = expression(name)
    packed = evaluate(node)
    # Cross-check that the addition expression really concatenates disjoint
    # literal bit ranges, without carries or accidental gaps in the chunk order.
    ordered = sorted(positions(node), key=lambda item: item[1])
    assert len({name for name, _ in ordered}) == len(ordered)
    for (lower, lo), (_, hi) in zip(ordered, ordered[1:]):
        assert literals[lower] < 2 ** (hi - lo)
    assert packed.bit_length() <= width * length
    raw = packed.to_bytes((width * length + 7) // 8, 'little')
    size = (width + 14) // 8
    mask = (1 << width) - 1
    lanes = []
    for index in range(length):
        bit = width * index
        lanes.append((int.from_bytes(raw[bit // 8:bit // 8 + size], 'little')
                      >> (bit % 8)) & mask)
    # Check both endpoints directly against the definition packed / 2^bit % 2^width.
    assert lanes[0] == packed % (1 << width)
    assert lanes[-1] == (packed // (1 << (width * (length - 1)))) % (1 << width)
    return lanes, dict(positions(node)), packed.bit_length()


classes, offsets, bit_length = unpack('rawClass', 12, 4**10)
representatives, _, _ = unpack('representatives', 20, 3741)
destinations, _, _ = unpack('destinations', 12, 3741 * 4)
kinds, _, _ = unpack('edgeKinds', 2, 3741 * 4)
print('Parsed all 786 literal definitions and all four assembly expressions.')
print('Packed rawClass bit length:', bit_length)
assert max(classes) == 3741
assert max(representatives) < 4**10
assert max(destinations) <= 3741
for dest, kind in zip(destinations, kinds):
    assert (dest == 0) == (kind == 3)
    assert dest == 0 or kind < 3

STEPS = ((1, 0), (0, 1), (-1, 0), (0, -1))


def bond(x, y):
    return tuple(sorted((x, y)))


def decode(code):
    return tuple((code // 4**(9 - i)) % 4 for i in range(10))


def geometry(code):
    word = decode(code)
    vertices = [(0, 0)]
    used = set()
    for direction in word:
        x, y = vertices[-1]
        dx, dy = STEPS[direction]
        end = (x + dx, y + dy)
        edge = bond(vertices[-1], end)
        assert edge not in used, ('non-raw representative', code)
        used.add(edge)
        vertices.append(end)
    return word, vertices, used


def row(word, vertices, used):
    end = vertices[-1]
    arrival = word[-1]
    revisit = end in vertices[:-1]
    allowed = []
    kind = []
    for direction, (dx, dy) in enumerate(STEPS):
        new = (end[0] + dx, end[1] + dy)
        allowed.append(direction != (arrival + 2) % 4 and bond(end, new) not in used)
        kind.append(2 if revisit else (0 if direction == arrival else 1))
    return arrival, allowed, kind


rep_rows = []
for a, code in enumerate(representatives):
    assert classes[code] == a, ('representative does not map to itself', a, code)
    rep_rows.append(row(*geometry(code)))
    _, allowed, kind = rep_rows[-1]
    for d in range(4):
        assert (destinations[4*a+d] != 0) == allowed[d], ('representative admissibility', a, d)
        if allowed[d]:
            assert kinds[4*a+d] == kind[d], ('representative kind', a, d)
            successor = (code % 4**9) * 4 + d
            assert classes[successor] + 1 == destinations[4*a+d], ('representative successor', a, d)
print('All 3741 representatives are raw words, map to their own class, and regenerate every stored row.')

raw_codes = set()
depth_counts = Counter()
comparison_counts = Counter()


def generate(word=(), vertices=((0, 0),), used=frozenset(), code=0):
    depth_counts[len(word)] += 1
    if len(word) == 10:
        raw_codes.add(code)
        a = classes[code]
        assert a < 3741, ('missing raw word', code, a)
        arrival, allowed, kind = row(word, vertices, used)
        rep_arrival, rep_allowed, rep_kind = rep_rows[a]
        assert allowed == rep_allowed, ('raw admissibility mismatch', code, a)
        assert kind == rep_kind, ('raw kind mismatch, including forbidden directions', code, a)
        for d in range(4):
            comparison_counts['all direction comparisons'] += 1
            if allowed[d]:
                successor = (code % 4**9) * 4 + d
                assert classes[successor] < 3741, ('successor not raw', code, d)
                assert classes[successor] + 1 == destinations[4*a+d], ('raw successor mismatch', code, a, d)
                comparison_counts['allowed successor comparisons'] += 1
                if kind[d] != 2:
                    assert arrival == rep_arrival, ('arrival mismatch', code, a, d)
                    comparison_counts['nonrevisit arrival comparisons'] += 1
        return
    start = vertices[-1]
    for d, (dx, dy) in enumerate(STEPS):
        end = (start[0] + dx, start[1] + dy)
        edge = bond(start, end)
        if edge not in used:
            generate(word + (d,), vertices + (end,), used | {edge}, 4*code+d)


generate()
assert len(raw_codes) == 60092
assert [depth_counts[i] for i in range(1, 11)] == [4, 12, 36, 108, 316, 916, 2628, 7500, 21268, 60092]
for code, a in enumerate(classes):
    assert (a < 3741) == (code in raw_codes), ('raw coverage mismatch', code, a)
assert {classes[code] for code in raw_codes} == set(range(3741))
print('Raw window counts at depths 1..10:', [depth_counts[i] for i in range(1, 11)])
print('Full coverage:', len(raw_codes), 'raw words and', len(classes) - len(raw_codes), 'invalid words, with sentinel 3741.')
print('Full quotient comparisons:', dict(comparison_counts))
edge_counts = Counter(kind for dest, kind in zip(destinations, kinds) if dest != 0)
assert edge_counts == {0: 2516, 1: 5032, 2: 1872}
print('Labelled class edge counts:', dict(sorted(edge_counts.items())))

for index in range(60, 65):
    name = f'rawClass_{index}'
    lo = offsets[name]
    hi = lo + 16384 - 1
    first, last = lo // 12, hi // 12
    full_first = (lo + 11) // 12
    full_last = (hi - 11) // 12
    codes = range(first, last + 1)
    valid = [c for c in codes if c in raw_codes]
    print(name, {
        'bit_range_inclusive': [lo, hi],
        'code_range_inclusive': [first, last],
        'complete_code_range_inclusive': [full_first, full_last],
        'first_lane_bits_in_chunk': min(12, 12 - lo % 12),
        'last_lane_bits_in_chunk': hi % 12 + 1,
        'overlapping_raw_codes': len(valid),
        'overlapping_invalid_codes': len(codes) - len(valid),
        'first_raw_code_class': [valid[0], classes[valid[0]]] if valid else None,
        'last_raw_code_class': [valid[-1], classes[valid[-1]]] if valid else None,
    })

# The archive is not an allowed input. Reconstruct the plain decimal table
# in its natural format and report whether the embedded source hash matches.
lines = ['60092 3741']
lines += [f'{code} {classes[code]}' for code in sorted(raw_codes)]
for a, code in enumerate(representatives):
    dest = [destinations[4*a+d] - 1 for d in range(4)]
    kind = [kinds[4*a+d] if destinations[4*a+d] else -1 for d in range(4)]
    lines.append(' '.join(map(str, [code, *dest, *kind])))
digest = sha256(('\n'.join(lines) + '\n').encode()).hexdigest()
print('Reconstructed archive SHA-256:', digest)
embedded = re.search(r'Archive SHA-256: ([0-9a-f]+)', text).group(1)
print('Matches source-file archive SHA-256:', digest == embedded)
print('ALL FINITE RECONSTRUCTION CHECKS PASSED')
