"""Read-only fidelity check of the five assigned packed table chunks."""

from pathlib import Path
import re


SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
source = SOURCE.read_text()
literal_pattern = re.compile(
    r'^private noncomputable def (\w+) : ℕ := 0x([0-9a-f]+)$', re.M
)
literals = {m[1]: int(m[2], 16) for m in literal_pattern.finditer(source)}
widths = {m[1]: 4 * len(m[2]) for m in literal_pattern.finditer(source)}


def unpack_expression(expression):
    """Parse the fully parenthesized source, preserving every leaf's bit offset."""
    tokens = re.findall(r'\w+|<<<|[()+]', expression)
    assert ''.join(tokens) == re.sub(r'\s', '', expression)
    cursor = 0

    def parse():
        nonlocal cursor
        token = tokens[cursor]
        cursor += 1
        if token != '(':
            if token.isdecimal():
                return int(token), []
            return literals[token], [(token, 0)]
        left, left_leaves = parse()
        operator = tokens[cursor]
        cursor += 1
        right, right_leaves = parse()
        assert tokens[cursor] == ')'
        cursor += 1
        if operator == '<<<':
            assert not right_leaves
            return left << right, [(name, offset + right) for name, offset in left_leaves]
        assert operator == '+'
        assert left & right == 0, 'Packing has a carry/overlapping nonzero bits'
        return left + right, left_leaves + right_leaves

    value, leaves = parse()
    assert cursor == len(tokens)
    next_offset = 0
    for name, offset in sorted(leaves, key=lambda leaf: leaf[1]):
        assert offset == next_offset, 'Gap or overlap between literal blocks'
        next_offset += widths[name]
    return value, dict(leaves), next_offset


tables = {}
for family in ('rawClass', 'representatives', 'destinations', 'edgeKinds'):
    expression = re.search(
        rf'^noncomputable def {family} : ℕ := (.*)$', source, re.M
    )[1]
    tables[family] = unpack_expression(expression)
    value, leaves, total_width = tables[family]
    print(f'{family}: {len(leaves)} contiguous literal blocks; {total_width} stored bits')

packed, offsets, _ = tables['rawClass']
steps = ((1, 0), (0, 1), (-1, 0), (0, -1))


def word(code):
    return tuple((code // 4**(9 - index)) % 4 for index in range(10))


def raw_window(directions):
    vertex = (0, 0)
    used = set()
    for direction in directions:
        dx, dy = steps[direction]
        next_vertex = (vertex[0] + dx, vertex[1] + dy)
        bond = frozenset((vertex, next_vertex))
        if bond in used:
            return False
        used.add(bond)
        vertex = next_vertex
    return True


for number in range(390, 395):
    name = f'rawClass_{number}'
    offset = offsets[name]
    width = widths[name]
    first_code = offset // 12
    last_code = (offset + width - 1) // 12
    phase = offset % 12
    lane_count = (width + phase + 11) // 12
    sentinel_pattern = 3741 * ((1 << (12 * lane_count)) - 1) // ((1 << 12) - 1)
    expected_literal = (sentinel_pattern >> phase) & ((1 << width) - 1)
    assert literals[name] == expected_literal
    for code in range(first_code, last_code + 1):
        directions = word(code)
        assert directions[:2] == (1, 3), 'Expected initial N,S reversal'
        assert not raw_window(directions)
        assert ((packed >> (12 * code)) & 4095) == 3741
    print(
        f'{name}: bits [{offset}, {offset + width}); phase {phase}; '
        f'codes [{first_code}, {last_code}]; '
        f'{last_code - first_code + 1} lanes touched; '
        'all sentinel 3741; all words begin N,S and repeat their first bond'
    )

print('PASS: all five complete literals and every touched boundary lane checked')
