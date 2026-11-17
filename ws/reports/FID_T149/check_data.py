"""Independent finite check of the packed data, reading only the permitted Lean input."""
from collections import Counter
from pathlib import Path
import json
import re

SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
text = SOURCE.read_text()
literals = {
    name: int(digits, 16)
    for name, digits in re.findall(
        r'^private noncomputable def (\w+) : ℕ := 0x([0-9a-f]+)$', text, re.M)
}


def expression(name):
    body = re.search(r'^noncomputable def ' + name + r' : ℕ := (.+)$', text, re.M)[1]
    tokens = re.findall(r'<<<|\w+|[()+]', body)
    assert ''.join(tokens) == re.sub(r'\s+', '', body)
    cursor = 0

    def parse():
        nonlocal cursor
        token = tokens[cursor]
        cursor += 1
        if token != '(':
            return int(token) if token.isdecimal() else token
        left = parse()
        if tokens[cursor] == ')':
            cursor += 1
            return left
        operation = tokens[cursor]
        cursor += 1
        assert operation in ('+', '<<<')
        right = parse()
        assert tokens[cursor] == ')'
        cursor += 1
        return (operation, left, right)

    tree = parse()
    assert cursor == len(tokens)
    return tree


def evaluate(tree):
    if isinstance(tree, int):
        return tree
    if isinstance(tree, str):
        return literals[tree]
    operation, left, right = tree
    if operation == '+':
        return evaluate(left) + evaluate(right)
    return evaluate(left) << evaluate(right)


def placements(tree, offset=0):
    if isinstance(tree, str):
        return [(tree, offset)]
    operation, left, right = tree
    if operation == '+':
        return placements(left, offset) + placements(right, offset)
    assert isinstance(right, int)
    return placements(left, offset + right)


def lanes(packed, width, count):
    blob = packed.to_bytes((width * count + 7) // 8, 'little')
    mask = (1 << width) - 1
    return [
        (int.from_bytes(blob[(width * i) // 8:(width * i + width + 7) // 8], 'little')
         >> ((width * i) % 8)) & mask
        for i in range(count)
    ]


raw_tree = expression('rawClass')
raw_placements = placements(raw_tree)
raw_hex = dict(re.findall(r'^private noncomputable def (rawClass_\d+) : ℕ := 0x([0-9a-f]+)$', text, re.M))
assert raw_placements == [
    ('rawClass_' + str(i), sum(4 * len(raw_hex['rawClass_' + str(j)]) for j in range(i + 1, 768)))
    for i in range(768)
]
assert all(0 <= literals[name] < 2**16384 for name, _ in raw_placements)
raw = lanes(evaluate(raw_tree), 12, 4**10)
representatives = lanes(evaluate(expression('representatives')), 20, 3741)
destinations = lanes(evaluate(expression('destinations')), 12, 3741 * 4)
kinds = lanes(evaluate(expression('edgeKinds')), 2, 3741 * 4)
assert len(set(representatives)) == 3741

steps = ((1, 0), (0, 1), (-1, 0), (0, -1))


def edge(x, y):
    return tuple(sorted((x, y)))


def next_point(x, d):
    return x[0] + steps[d][0], x[1] + steps[d][1]


def decode(code):
    return [(code // 4**(9 - i)) % 4 for i in range(10)]


def regenerate(code):
    word = decode(code)
    vertices = [(0, 0)]
    bonds = set()
    for d in word:
        y = next_point(vertices[-1], d)
        b = edge(vertices[-1], y)
        assert b not in bonds, ('invalid representative', code)
        bonds.add(b)
        vertices.append(y)
    return row(code, vertices, bonds)


def row(code, vertices, bonds):
    arrival = code % 4
    revisit = vertices[-1] in vertices[:-1]
    allowed = [d != (arrival + 2) % 4 and
               edge(vertices[-1], next_point(vertices[-1], d)) not in bonds
               for d in range(4)]
    kind = [2 if revisit else (0 if d == arrival else 1) for d in range(4)]
    successor = [(code % 4**9) * 4 + d for d in range(4)]
    return allowed, kind, successor, arrival


rep_rows = [regenerate(c) for c in representatives]
for a, c in enumerate(representatives):
    assert raw[c] == a, ('representative class', a, c, raw[c])
    allow, kind, successor, arrival = rep_rows[a]
    for d in range(4):
        e = 4 * a + d
        assert 0 <= destinations[e] <= 3741
        assert (destinations[e] == 0) == (kinds[e] == 3)
        assert (destinations[e] != 0) == allow[d]
        if allow[d]:
            assert kinds[e] == kind[d]
            assert destinations[e] - 1 == raw[successor[d]]

target_chunks = {}
for i in range(710, 715):
    offset = dict(raw_placements)['rawClass_' + str(i)]
    low = offset // 12
    high = (offset + 16383) // 12
    target_chunks[i] = {
        'bit_offset': offset,
        'codes_touched_inclusive': [low, high],
        'complete_lanes_inclusive': [(offset + 11) // 12, (offset + 16384) // 12 - 1],
        'valid_codes': [],
    }

seen = bytearray(4**10)
class_sizes = Counter()
depth_counts = Counter()
errors = []


def generate(code, vertices, bonds):
    depth = len(vertices) - 1
    depth_counts[depth] += 1
    if depth < 10:
        for d in range(4):
            y = next_point(vertices[-1], d)
            b = edge(vertices[-1], y)
            if b not in bonds:
                bonds.add(b)
                vertices.append(y)
                generate(code * 4 + d, vertices, bonds)
                vertices.pop()
                bonds.remove(b)
        return
    seen[code] = 1
    a = raw[code]
    assert 0 <= a < 3741, ('raw class range', code, a)
    class_sizes[a] += 1
    allow, kind, successor, arrival = row(code, vertices, bonds)
    rep_allow, rep_kind, rep_successor, rep_arrival = rep_rows[a]
    assert allow == rep_allow, ('admissibility', code, a)
    # This also checks kinds on forbidden directions, as in the lemma's hypotheses.
    assert kind == rep_kind, ('kind', code, a)
    for d in range(4):
        if allow[d]:
            assert raw[successor[d]] == destinations[4 * a + d] - 1, ('successor', code, d)
            if kind[d] != 2:
                assert arrival == rep_arrival, ('arrival', code, a)
    for result in target_chunks.values():
        low, high = result['codes_touched_inclusive']
        if low <= code <= high:
            result['valid_codes'].append(code)


generate(0, [(0, 0)], set())
assert sorted(class_sizes) == list(range(3741))
for code, a in enumerate(raw):
    assert a <= 3741
    assert (a < 3741) == bool(seen[code]), ('coverage', code, a, seen[code])

edge_counts = Counter(k for a, k in zip(destinations, kinds) if a != 0)
assert edge_counts == {0: 2516, 1: 5032, 2: 1872}

for result in target_chunks.values():
    low, high = result['codes_touched_inclusive']
    codes = result.pop('valid_codes')
    result['lanes_touched'] = high - low + 1
    result['raw_window_lanes'] = len(codes)
    result['invalid_lanes'] = high - low + 1 - len(codes)
    result['classes_on_valid_lanes'] = sorted({raw[c] for c in codes})
    result['first_valid_examples'] = [
        {'code': c, 'directions': ''.join('ENWS'[d] for d in decode(c)), 'class': raw[c],
         'representative': representatives[raw[c]]}
        for c in codes[:3]
    ]

output = {
    'raw_chunks': len(raw_placements),
    'chunk_width_bits': 16384,
    'last_chunk_width_bits': 4 * len(raw_hex['rawClass_767']),
    'raw_lanes': len(raw),
    'raw_lane_width_bits': 12,
    'sentinel': 3741,
    'raw_window_counts_by_length': dict(sorted(depth_counts.items())),
    'quotient_classes': len(class_sizes),
    'edge_counts': dict(edge_counts),
    'all_raw_coverage_representative_and_transition_checks_passed': True,
    'targets': target_chunks,
}
print(json.dumps(output, indent=2))
