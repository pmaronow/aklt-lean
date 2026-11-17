"""Exact, read-only reconstruction of the assigned packed-table fragments.

Run with Python 3. Reads only the supplied Lean source tree and writes nothing.
"""

from collections import Counter
from pathlib import Path
import re


SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
source = SOURCE.read_text()
literals = {}
literal_lines = {}
for number, line in enumerate(source.splitlines(), 1):
    match = re.fullmatch(
        r'private noncomputable def (\w+) : ℕ := 0x([0-9a-f]+)', line
    )
    if match:
        literals[match[1]] = int(match[2], 16)
        literal_lines[match[1]] = (number, len(match[2]))


def parse_table(name):
    expression = re.search(
        rf'^noncomputable def {name} : ℕ := (.+)$', source, re.M
    )[1]
    tokens = re.findall(r'\w+|<<<|[()+]', expression)
    assert ''.join(tokens) == re.sub(r'\s+', '', expression)
    position = 0

    def atom():
        nonlocal position
        token = tokens[position]
        position += 1
        if token == '(':
            node = addition()
            assert tokens[position] == ')'
            position += 1
            return node
        if token.isdecimal():
            return int(token)
        assert token in literals, token
        return token

    def shift():
        nonlocal position
        node = atom()
        while position < len(tokens) and tokens[position] == '<<<':
            position += 1
            amount = atom()
            assert isinstance(amount, int)
            node = ('shift', node, amount)
        return node

    def addition():
        nonlocal position
        node = shift()
        while position < len(tokens) and tokens[position] == '+':
            position += 1
            node = ('add', node, shift())
        return node

    tree = addition()
    assert position == len(tokens)
    offsets = {}

    def evaluate(node, offset=0):
        if isinstance(node, str):
            assert node not in offsets
            offsets[node] = offset
            return literals[node]
        if node[0] == 'shift':
            return evaluate(node[1], offset + node[2]) << node[2]
        return evaluate(node[1], offset) + evaluate(node[2], offset)

    value = evaluate(tree)
    ordered = sorted(offsets, key=offsets.get)
    for low, high in zip(ordered, ordered[1:]):
        assert literals[low].bit_length() <= offsets[high] - offsets[low]
    return value, offsets


tables = {name: parse_table(name) for name in
          ('rawClass', 'representatives', 'destinations', 'edgeKinds')}
assert len(literals) == 768 + 5 + 11 + 2
assert set(literals) == {key for _, offsets in tables.values() for key in offsets}
raw, offsets = tables['rawClass']
assert len(offsets) == 768
assert set(offsets) == {f'rawClass_{i}' for i in range(768)}
raw_bytes = raw.to_bytes((raw.bit_length() + 7) // 8, 'little')


def lane(code):
    byte = (12 * code) // 8
    return (int.from_bytes(raw_bytes[byte:byte + 3], 'little') >>
            ((12 * code) % 8)) & 4095


def word(code):
    return tuple((code >> (2 * (9 - i))) & 3 for i in range(10))


def raw_window(code):
    """Injectivity of Finset-valued wordBond, using integer coordinates."""
    point = (0, 0)
    bonds = set()
    steps = ((1, 0), (0, 1), (-1, 0), (0, -1))
    for direction in word(code):
        step = steps[direction]
        nxt = (point[0] + step[0], point[1] + step[1])
        bond = frozenset((point, nxt))
        if bond in bonds:
            return False
        bonds.add(bond)
        point = nxt
    return True


marker = 3741
periodic = sum(marker << (12 * i) for i in range(1368))
affected = set()
for i in range(285, 290):
    name = f'rawClass_{i}'
    line, digits = literal_lines[name]
    offset = offsets[name]
    width = 4 * digits
    assert width == 16384
    expected = (periodic >> (offset % 12)) & ((1 << width) - 1)
    assert literals[name] == expected
    first = offset // 12
    last = (offset + width - 1) // 12
    codes = range(first, last + 1)
    counts = Counter(lane(code) for code in codes)
    valid = [code for code in codes if raw_window(code)]
    reversals = [code for code in codes
                 if not any((b - a) % 4 == 2
                            for a, b in zip(word(code), word(code)[1:]))]
    assert counts == {marker: len(codes)}
    assert not valid
    assert not reversals
    affected.update(codes)
    prefixes = sorted({''.join('ENWS'[d] for d in word(code)[:4])
                       for code in codes})
    print(f'{name} line={line}: bits [{offset},{offset + width}); '
          f'codes [{first},{last}], {len(codes)} intersecting lanes; '
          f'values={dict(counts)}, raw_windows={len(valid)}, '
          f'no_adjacent_reversal={len(reversals)}, prefixes={prefixes}')

assert affected == set(range(min(affected), max(affected) + 1))
print(f'Union: {len(affected)} distinct codes, '
      f'{min(affected)}..{max(affected)}, all invalid.')
print(f'Parsed all {len(literals)} literal declarations and all four '
      'assembly expressions; no overlapping summands.')

# Independent generation of the exact paper domain, without reading any archive.
raw_codes = set()
depth_counts = Counter()
steps = ((1, 0), (0, 1), (-1, 0), (0, -1))


def generate(depth, point, bonds, code):
    depth_counts[depth] += 1
    if depth == 10:
        raw_codes.add(code)
        return
    for direction, (dx, dy) in enumerate(steps):
        nxt = (point[0] + dx, point[1] + dy)
        bond = frozenset((point, nxt))
        if bond not in bonds:
            generate(depth + 1, nxt, bonds | {bond}, 4 * code + direction)


generate(0, (0, 0), set(), 0)
assert [depth_counts[i] for i in range(1, 11)] == [
    4, 12, 36, 108, 316, 916, 2628, 7500, 21268, 60092
]
assert not (raw_codes & affected)
print('Independent depth counts:', [depth_counts[i] for i in range(1, 11)])

# Context check: ensure the table's invalid marker has the stated meaning.
distribution = Counter()
coverage_errors = []
for code in range(4 ** 10):
    value = lane(code)
    distribution[value == marker] += 1
    if value > marker or (value < marker) != (code in raw_codes):
        coverage_errors.append((code, value))
assert not coverage_errors
print('Whole-table coverage: 60092 raw codes have class <3741; '
      f'{distribution[True]} other codes have marker 3741; no errors.')
