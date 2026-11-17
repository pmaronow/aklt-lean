"""Exact finite check for FID_T077; reads only the assigned Lean input."""
from pathlib import Path
import re

source = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean').read_text()
chunks = {
    int(i): h for i, h in re.findall(
        r'^private noncomputable def rawClass_(\d+) : ℕ := 0x([0-9a-f]+)$',
        source, re.M)
}
expression = re.search(r'^noncomputable def rawClass : ℕ := (.*)$', source, re.M)[1]
tokens = re.findall(r'rawClass_\d+|<<<|[()+]|\d+', expression)
assert ''.join(tokens) == re.sub(r'\s+', '', expression)
position = 0


def atom():
    global position
    token = tokens[position]
    position += 1
    if token == '(':
        result = parse()
        assert tokens[position] == ')'
        position += 1
        return result
    assert token.startswith('rawClass_')
    return {int(token.split('_')[1]): 0}


def parse():
    global position
    result = atom()
    operators = 0
    while position < len(tokens) and tokens[position] != ')':
        operation = tokens[position]
        position += 1
        operators += 1
        # Each parenthesized expression has one operation, so no precedence
        # assumption enters this reconstruction.
        assert operators == 1
        if operation == '<<<':
            shift = int(tokens[position])
            position += 1
            result = {i: offset + shift for i, offset in result.items()}
        else:
            assert operation == '+'
            other = atom()
            assert not result.keys() & other.keys()
            result.update(other)
    return result


offsets = parse()
assert position == len(tokens)
assert set(offsets) == set(chunks) == set(range(768))
intervals = sorted((offsets[i], offsets[i] + 4 * len(h), i) for i, h in chunks.items())
assert intervals[0][0] == 0
assert all(a[1] == b[0] for a, b in zip(intervals, intervals[1:]))
# The verified shifts concatenate the hex strings, most significant first.
packed_hex = ''.join(chunks[i] for _, _, i in reversed(intervals)).zfill(3 * 4**10)
assert len(packed_hex) == 3 * 4**10


def lane(code):
    end = len(packed_hex) - 3 * code
    return int(packed_hex[end - 3:end], 16)


def word(code):
    return tuple((code // 4**(9 - i)) % 4 for i in range(10))


all_codes = set()
print('Entire rawClass aggregation: 768 disjoint, contiguous chunks; no overlap/carry.')
print('Bit positions are zero based, least significant first; code intervals inclusive.')
for i in range(350, 355):
    offset = offsets[i]
    width = 4 * len(chunks[i])
    expected = sum(((3741 >> ((offset + j) % 12)) & 1) << j for j in range(width))
    assert int(chunks[i], 16) == expected
    low, high = offset // 12, (offset + width - 1) // 12
    for code in range(low, high + 1):
        assert lane(code) == 3741  # Includes lanes crossing chunk boundaries.
        directions = word(code)
        assert directions[:2] == (2, 0)  # West then east.
        # Recompute all ten unoriented bonds directly in the integer plane.
        steps = ((1, 0), (0, 1), (-1, 0), (0, -1))
        vertex = (0, 0)
        bonds = []
        for direction in directions:
            step = steps[direction]
            next_vertex = (vertex[0] + step[0], vertex[1] + step[1])
            bonds.append(frozenset((vertex, next_vertex)))
            vertex = next_vertex
        assert bonds[0] == bonds[1]
        assert len(set(bonds)) < 10
        all_codes.add(code)
    print(f'rawClass_{i}: bits {offset}..{offset + width - 1}; '
          f'codes {low}..{high}; exact sentinel slice and all full lanes PASS; '
          f'all words begin W,E and repeat their first bond PASS')
print(f'Unique affected words checked: {len(all_codes)}; all invalid; all lanes 3741.')
