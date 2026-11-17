"""Read-only arithmetic and raw-window checks for FID_T078."""

import ast
from pathlib import Path
import re


SOURCE = Path(
    "/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean"
)
source = SOURCE.read_text()
hex_chunks = {
    match[1]: match[2]
    for match in re.finditer(
        r"private noncomputable def (rawClass_\d+) : ℕ := 0x([0-9a-f]+)",
        source,
    )
}
expression = re.search(r"noncomputable def rawClass : ℕ := (.*)", source)[1]


def offsets(node):
    if isinstance(node, ast.Name):
        return {node.id: 0}
    assert isinstance(node, ast.BinOp)
    if isinstance(node.op, ast.LShift):
        assert isinstance(node.right, ast.Constant)
        return {name: bit + node.right.value for name, bit in offsets(node.left).items()}
    assert isinstance(node.op, ast.Add)
    left, right = offsets(node.left), offsets(node.right)
    assert not left.keys() & right.keys()
    return left | right


positions = offsets(ast.parse(expression.replace("<<<", "<<"), mode="eval").body)
assert set(positions) == set(hex_chunks) == {f"rawClass_{i}" for i in range(768)}
next_bit = 0
for name in sorted(positions, key=positions.get):
    assert positions[name] == next_bit
    next_bit += 4 * len(hex_chunks[name])
packed_hex = "".join(hex_chunks[f"rawClass_{i}"] for i in range(768))
assert len(packed_hex) * 4 == next_bit
packed_hex = packed_hex.zfill(3 * 4**10)
assert len(packed_hex) == 3 * 4**10


def lane(code):
    end = len(packed_hex) - 3 * code
    return int(packed_hex[end - 3 : end], 16)


affected = set()
# A periodic e9d bit string is the invalid-code sentinel 3741 in each lane.
periodic_sentinel = sum(3741 << (12 * i) for i in range(1368))
for number in range(355, 360):
    name = f"rawClass_{number}"
    low = positions[name]
    width = 4 * len(hex_chunks[name])
    high = low + width - 1
    assert width == 16384
    expected = (periodic_sentinel >> (low % 12)) & ((1 << width) - 1)
    assert int(hex_chunks[name], 16) == expected
    codes = range(low // 12, high // 12 + 1)
    assert all(lane(code) == 3741 for code in codes)
    # Most-significant base-four digits are 2,0, i.e. west then east.
    assert all(code // 4**8 == 8 for code in codes)
    affected.update(codes)
    print(f"{name}: bits {low}..{high}; codes {codes.start}..{codes.stop - 1}; "
          "all assembled lanes 3741; all prefixes W,E")

# Independently generate exactly the bond-injective words of lengths 1..10.
steps = ((1, 0), (0, 1), (-1, 0), (0, -1))
counts = [0] * 11
intersections = []
used = set()


def generate(depth, position, code):
    counts[depth] += 1
    if depth == 10:
        if code in affected:
            intersections.append(code)
        return
    for direction, step in enumerate(steps):
        successor = (position[0] + step[0], position[1] + step[1])
        bond = frozenset((position, successor))
        if bond in used:
            continue
        used.add(bond)
        generate(depth + 1, successor, 4 * code + direction)
        used.remove(bond)


generate(0, (0, 0), 0)
assert counts[1:] == [4, 12, 36, 108, 316, 916, 2628, 7500, 21268, 60092]
assert not intersections
print("Regenerated raw-window counts:", counts[1:])
print(f"Distinct affected codes: {len(affected)}; raw windows among them: 0")
print("All checks passed.")
