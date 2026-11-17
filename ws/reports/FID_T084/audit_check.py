"""Reconstruct the supplied tables and check the five assigned packed fragments.

Reads only the supplied Lean input. Uses exact Python integers and independently
generates the paper's distinct-unoriented-bond windows.
"""

import ast
from collections import Counter
from pathlib import Path
import re


SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
source = SOURCE.read_text()
literals = {
    name: int(value, 16)
    for name, value in re.findall(
        r'^private noncomputable def (\w+) : ℕ := (0x[0-9a-f]+)$',
        source, re.MULTILINE,
    )
}
hex_literals = dict(re.findall(
    r'^private noncomputable def (\w+) : ℕ := 0x([0-9a-f]+)$',
    source, re.MULTILINE,
))


def expression(name):
    match = re.search(r'^noncomputable def ' + name + r' : ℕ := (.+)$',
                      source, re.MULTILINE)
    return ast.parse(match[1].replace('<<<', '<<'), mode='eval').body


def terms(node, offset=0):
    if isinstance(node, ast.Name):
        return [(node.id, offset)]
    assert isinstance(node, ast.BinOp)
    if isinstance(node.op, ast.LShift):
        assert isinstance(node.right, ast.Constant)
        return terms(node.left, offset + node.right.value)
    assert isinstance(node.op, ast.Add)
    return terms(node.left, offset) + terms(node.right, offset)


tables = {}
positions = {}
for name in ['rawClass', 'representatives', 'destinations', 'edgeKinds']:
    leaves = terms(expression(name))
    # Check every shift: the expression must concatenate all declared hex
    # fragments in exactly their written order, preserving leading zeroes.
    assert [key for key, _ in leaves] == [
        f'{name}_{i}' for i in range(len(leaves))]
    offset = 0
    for key, actual_offset in reversed(leaves):
        assert actual_offset == offset, (key, actual_offset, offset)
        positions[key] = actual_offset
        offset += 4 * len(hex_literals[key])
    packed = int(''.join(hex_literals[key] for key, _ in leaves), 16)
    assembled = sum(literals[key] << offset for key, offset in leaves)
    assert packed == assembled
    tables[name] = packed
    print(f'{name}: {len(leaves)} fragments; all assembly offsets checked; '
          f'{packed.bit_length()} significant bits')

# Pad the high zero nibble, then use three hex digits per 12-bit raw lane.
raw_hex = format(tables['rawClass'], f'0{3 * 4**10}x')
assert len(raw_hex) == 3 * 4**10


def raw_class(code):
    end = len(raw_hex) - 3 * code
    return int(raw_hex[end - 3:end], 16)


def lane(name, width, index):
    return (tables[name] >> (width * index)) & ((1 << width) - 1)


steps = [(1, 0), (0, 1), (-1, 0), (0, -1)]


def decode(code):
    return tuple((code // 4**i) % 4 for i in reversed(range(10)))


def first_repeated_bond(code):
    vertex = (0, 0)
    used = {}
    for i, d in enumerate(decode(code), 1):
        dx, dy = steps[d]
        next_vertex = (vertex[0] + dx, vertex[1] + dy)
        bond = frozenset([vertex, next_vertex])
        if bond in used:
            return used[bond], i
        used[bond] = i
        vertex = next_vertex
    return None


# Independent generation of exactly the paper's Omega_j (no virtual bond).
states = [(0, (0, 0), frozenset())]
counts = []
for length in range(1, 11):
    next_states = []
    for code, (x, y), used in states:
        for d, (dx, dy) in enumerate(steps):
            endpoint = (x + dx, y + dy)
            bond = frozenset([(x, y), endpoint])
            if bond not in used:
                next_states.append((4 * code + d, endpoint, used | {bond}))
    states = next_states
    counts.append(len(states))
valid_codes = {code for code, _, _ in states}
assert counts == [4, 12, 36, 108, 316, 916, 2628, 7500, 21268, 60092]
print('Independent raw-window counts:', counts)

for i in range(385, 390):
    name = f'rawClass_{i}'
    offset = positions[name]
    width = 4 * len(hex_literals[name])
    low, high = offset // 12, (offset + width - 1) // 12
    full_low, full_high = (offset + 11) // 12, (offset + width) // 12 - 1
    codes = range(low, high + 1)
    assert not valid_codes.intersection(codes)
    assert all(first_repeated_bond(code) is not None for code in codes)
    assert all(raw_class(code) == 3741 for code in codes)
    # Check every fragment bit, including its partial lanes at both boundaries.
    expected = 0
    for code in codes:
        expected |= 3741 << (12 * code - 12 * low)
    expected = (expected >> (offset - 12 * low)) & ((1 << width) - 1)
    assert literals[name] == expected
    print(f'{name}: bit interval [{offset}, {offset + width}); '
          f'intersecting codes [{low}, {high}] ({high - low + 1}); '
          f'complete lanes [{full_low}, {full_high}]; '
          f'valid windows 0; every intersecting lane = 3741 = 0xe9d; '
          f'repeated-bond positions {dict(Counter(first_repeated_bond(c) for c in codes))}; '
          f'first-five-direction prefixes {sorted({decode(c)[:5] for c in codes})}')

# Sanity checks on all lanes and on the raw definition used by the interface.
coverage_errors = [code for code in range(4**10)
                   if raw_class(code) > 3741
                   or ((raw_class(code) < 3741) != (code in valid_codes))]
assert not coverage_errors
print('All 1,048,576 raw lanes: range and valid-window/sentinel coverage pass.')
print('Review scope: rawClass_385 through rawClass_389 only.')
