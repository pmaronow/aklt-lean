"""Read-only check of the five assigned packed class-map segments."""

import ast
import re
from pathlib import Path


SOURCE = Path(
    "/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean"
)
source = SOURCE.read_text()
literals = {
    name: (int(digits, 16), 4 * len(digits))
    for name, digits in re.findall(
        r"private noncomputable def (\w+) : ℕ := 0x([0-9a-f]+)", source
    )
}
expression = re.search(r"^noncomputable def rawClass : ℕ := (.*)$", source, re.M)[1]
tree = ast.parse(expression.replace("<<<", "<<"), mode="eval").body


def unpack_expression(node, offset=0):
    """Evaluate only names, parenthesized shifts, and additions; retain offsets."""
    if isinstance(node, ast.Name):
        value, width = literals[node.id]
        return value << offset, [(node.id, offset, width)]
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.LShift):
        assert isinstance(node.right, ast.Constant)
        assert isinstance(node.right.value, int) and node.right.value >= 0
        return unpack_expression(node.left, offset + node.right.value)
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add):
        left, left_offsets = unpack_expression(node.left, offset)
        right, right_offsets = unpack_expression(node.right, offset)
        return left + right, left_offsets + right_offsets
    raise AssertionError(ast.dump(node))


packed, positions = unpack_expression(tree)
assert len(positions) == 768
assert len({name for name, _, _ in positions}) == 768

# The slots abut without overlap. Addition therefore cannot carry into or
# overwrite any of the assigned segments, including their boundary bits.
end = 0
for name, offset, width in sorted(positions, key=lambda entry: entry[1]):
    assert offset == end
    assert 0 <= literals[name][0] < 1 << width
    end = offset + width

all_codes = set()
for number in range(655, 660):
    name = f"rawClass_{number}"
    _, offset, width = next(entry for entry in positions if entry[0] == name)
    assert width == 16384
    first = offset // 12
    last = (offset + width - 1) // 12
    codes = range(first, last + 1)
    all_codes.update(codes)

    # Construct precisely the expected sentinel bits, including partial lanes
    # at both ends, and compare every bit of the literal.
    expected = sum(3741 << (12 * i) for i in range(last - first + 1))
    expected = (expected >> (offset % 12)) & ((1 << width) - 1)
    assert literals[name][0] == expected

    for code in codes:
        assert 0 <= code < 4**10
        # MSF direction code: 0 = E, 1 = N, 2 = W, 3 = S.
        word = [(code // 4 ** (9 - i)) % 4 for i in range(10)]
        assert word[:2] == [0, 2]
        x = y = 0
        bonds = []
        for direction in word:
            dx, dy = [(1, 0), (0, 1), (-1, 0), (0, -1)][direction]
            next_vertex = (x + dx, y + dy)
            bonds.append(frozenset(((x, y), next_vertex)))
            x, y = next_vertex
        assert bonds[0] == bonds[1]
        assert len(set(bonds)) < 10
        assert ((packed >> (12 * code)) & 4095) == 3741

    print(
        f"{name}: PASS; line {15 + 2 * number}; bit offset {offset}; "
        f"{width} bits; touched codes {first}..{last}; "
        f"{len(codes)} lanes; all sentinel 3741 and non-raw"
    )

print(
    f"PASS: all 81920 assigned literal bits and {len(all_codes)} distinct "
    "touching lanes, including boundary lanes, checked."
)
