"""Read-only reconstruction of the literal tables and the five reviewed chunks."""

from collections import Counter
from pathlib import Path
import json
import re

SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
source = SOURCE.read_text()
literal_pattern = r'private noncomputable def (\w+) : ℕ := 0x([0-9a-f]+)'
hexes = dict(re.findall(literal_pattern, source))
values = {name: int(h, 16) for name, h in hexes.items()}


def assemble(expression):
    """Parse the parenthesized Lean +/<<< expressions and track leaf bit offsets."""
    tokens = re.findall(r'\w+|<<<|[()+]', expression)
    assert re.sub(r'\s+', '', expression) == ''.join(tokens)
    position = 0

    def atom():
        nonlocal position
        token = tokens[position]
        position += 1
        if token == '(':
            result = addition()
            assert tokens[position] == ')'
            position += 1
            return result
        if token.isdecimal():
            return int(token), []
        return values[token], [(token, 0)]

    def shift():
        nonlocal position
        value, leaves = atom()
        while position < len(tokens) and tokens[position] == '<<<':
            position += 1
            amount, unused = atom()
            assert not unused
            value <<= amount
            leaves = [(name, offset + amount) for name, offset in leaves]
        return value, leaves

    def addition():
        nonlocal position
        value, leaves = shift()
        while position < len(tokens) and tokens[position] == '+':
            position += 1
            right, right_leaves = shift()
            value += right
            leaves += right_leaves
        return value, leaves

    result = addition()
    assert position == len(tokens)
    return result


tables = {}
offsets = {}
for family in ('rawClass', 'representatives', 'destinations', 'edgeKinds'):
    expression = re.search(r'^noncomputable def ' + family + r' : ℕ := (.+)$', source, re.M)[1]
    value, leaves = assemble(expression)
    expected_names = [f'{family}_{i}' for i in range(sum(n.startswith(family + '_') for n in hexes))]
    assert [name for name, offset in leaves] == expected_names
    expected_offset = 0
    for name, offset in reversed(leaves):
        assert offset == expected_offset
        assert values[name] < 1 << (4 * len(hexes[name]))
        offsets[name] = offset
        expected_offset += 4 * len(hexes[name])
    assert value == int(''.join(hexes[name] for name in expected_names), 16)
    tables[family] = value

packed_bytes = tables['rawClass'].to_bytes((12 * 4**10 + 7) // 8, 'little')


def lane(code):
    bit = 12 * code
    return (int.from_bytes(packed_bytes[bit // 8:bit // 8 + 3], 'little') >> (bit % 8)) & 4095


def word(code):
    return tuple((code >> (2 * i)) & 3 for i in range(9, -1, -1))


def first_repeated_bond(directions):
    steps = ((1, 0), (0, 1), (-1, 0), (0, -1))
    used = set()
    x, y = 0, 0
    for i, d in enumerate(directions):
        dx, dy = steps[d]
        new = (x + dx, y + dy)
        bond = frozenset(((x, y), new))
        if bond in used:
            return i
        used.add(bond)
        x, y = new
    return None


results = []
all_codes = set()
for i in range(470, 475):
    name = f'rawClass_{i}'
    low = offsets[name]
    high = low + 4 * len(hexes[name]) - 1
    codes = range(low // 12, high // 12 + 1)
    markers = Counter(lane(code) for code in codes)
    repeated = Counter(first_repeated_bond(word(code)) for code in codes)
    assert markers == Counter({3741: len(codes)})
    assert repeated == Counter({2: len(codes)})
    assert all(word(code)[:3] == (1, 2, 0) for code in codes)
    # Check the actual chunk, including both partial lanes, against a run of
    # 12-bit markers at its absolute position in the full natural number.
    first = low // 12
    expected_run = 3741 * (((1 << (12 * len(codes))) - 1) // 4095)
    expected_chunk = (expected_run >> (low - 12 * first)) & ((1 << (high - low + 1)) - 1)
    assert values[name] == expected_chunk
    results.append(dict(declaration=name, line=source[:source.index('private noncomputable def ' + name + ' :')].count('\n') + 1,
                        low_bit=low, high_bit=high, first_code=codes.start, last_code=codes.stop - 1,
                        touched_lanes=len(codes), fully_contained_lanes=(high - 11) // 12 - (low + 11) // 12 + 1,
                        marker=3741, first_repeated_bond_index=2))
    all_codes.update(codes)

print(json.dumps(dict(parsed_literals=len(values),
                      assembly_checks='All four assembly expressions match ordered hexadecimal concatenation; no overlap or carry.',
                      reviewed=results, distinct_codes_checked=len(all_codes)), indent=2))
