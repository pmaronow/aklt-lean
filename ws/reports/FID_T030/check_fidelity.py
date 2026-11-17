"""Read-only, exact-integer audit of the five assigned packed-data limbs."""

import ast
from pathlib import Path
import re


SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
text = SOURCE.read_text()
literals = {
    name: (int(value, 16), 4 * (len(value) - 2))
    for name, value in re.findall(
        r'private noncomputable def (\w+) : ℕ := (0x[0-9a-fA-F]+)', text
    )
}


def assemble(name):
    """Evaluate only names, numerals, shifts, and sums; also track bit positions."""
    expression = re.search(
        rf'^noncomputable def {name} : ℕ := (.+)$', text, re.M
    ).group(1)

    def visit(node):
        if isinstance(node, ast.Name):
            value, width = literals[node.id]
            return value, [(node.id, 0, width)]
        if isinstance(node, ast.BinOp) and isinstance(node.op, ast.LShift):
            assert isinstance(node.right, ast.Constant)
            shift = node.right.value
            value, positions = visit(node.left)
            return value << shift, [(n, o + shift, w) for n, o, w in positions]
        if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add):
            left, left_positions = visit(node.left)
            right, right_positions = visit(node.right)
            assert left & right == 0, 'Overlapping nonzero bits in concatenation'
            return left + right, left_positions + right_positions
        raise AssertionError(ast.dump(node))

    packed, positions = visit(ast.parse(expression.replace('<<<', '<<'), mode='eval').body)
    cursor = 0
    for _, offset, width in sorted(positions, key=lambda p: p[1]):
        assert offset == cursor, 'Gap or overlap in allocated limb intervals'
        cursor += width
    return packed, {n: (o, w) for n, o, w in positions}, cursor


packed, positions, total_width = assemble('rawClass')
assert total_width <= 12 * 4**10
print(f'Parsed all {len(literals)} literal blocks and the complete rawClass expression.')
print(f'rawClass: {len(positions)} contiguous limbs, {total_width} allocated bits.')

# Turn the full table into fixed-width bytes once, to avoid repeatedly shifting
# a 12-million-bit integer. The 12-bit fields are little-endian as in lane.
data = packed.to_bytes((12 * 4**10) // 8, 'little')


def raw_class_at(code):
    bit = 12 * code
    byte, shift = divmod(bit, 8)
    return (int.from_bytes(data[byte:byte + 2], 'little') >> shift) & 4095


def directions(code):
    return [(code // 4**(9 - i)) % 4 for i in range(10)]


def raw_window(code):
    steps = [(1, 0), (0, 1), (-1, 0), (0, -1)]
    vertex = (0, 0)
    bonds = set()
    for d in directions(code):
        dx, dy = steps[d]
        next_vertex = (vertex[0] + dx, vertex[1] + dy)
        bond = frozenset((vertex, next_vertex))
        if bond in bonds:
            return False
        bonds.add(bond)
        vertex = next_vertex
    return True


for index in range(115, 120):
    name = f'rawClass_{index}'
    value, _ = literals[name]
    offset, width = positions[name]
    first, last = offset // 12, (offset + width - 1) // 12
    codes = range(first, last + 1)
    assert all(raw_class_at(c) == 3741 for c in codes)
    assert all(not raw_window(c) for c in codes)
    assert all(directions(c)[:2] == [3, 1] for c in codes)
    # Check every bit in the assigned literal against the expected sentinel
    # stream, including the partial 12-bit fields at limb boundaries.
    expected = sum(3741 << (12 * (c - first)) for c in codes)
    expected = (expected >> (offset - 12 * first)) & ((1 << width) - 1)
    assert value == expected
    print(f'{name}: bits [{offset},{offset + width}); codes {first}..{last} '
          f'({last - first + 1}); bit offset mod 12={offset % 12}; '
          'all fields 3741; all words begin S,N and repeat their first bond; '
          'full literal equals the expected sentinel bits.')

print('PASS: all five complete literals and their cross-limb boundary fields agree.')
