"""Reproduce the scoped packing and raw-window checks without running Lean."""

import ast
from pathlib import Path
import re


SOURCE = Path(
    "/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean"
)
source = SOURCE.read_text()
records = re.findall(
    r"^private noncomputable def (\w+) : ℕ := 0x([0-9a-f]+)$",
    source,
    re.MULTILINE,
)
values = {name: int(digits, 16) for name, digits in records}
raw_names = [name for name, _ in records if name.startswith("rawClass_")]
assert raw_names == [f"rawClass_{i}" for i in range(768)]
expression = re.search(
    r"^noncomputable def rawClass : ℕ := (.*)$", source, re.MULTILINE
)[1]


def reconstruct(node):
    """Evaluate natural addition/shift and track each literal's bit offset."""
    if isinstance(node, ast.Name):
        assert node.id in raw_names
        return values[node.id], {node.id: 0}
    assert isinstance(node, ast.BinOp)
    left, positions = reconstruct(node.left)
    if isinstance(node.op, ast.LShift):
        assert isinstance(node.right, ast.Constant)
        shift = node.right.value
        assert isinstance(shift, int) and shift >= 0
        return left << shift, {
            name: offset + shift for name, offset in positions.items()
        }
    assert isinstance(node.op, ast.Add)
    right, other_positions = reconstruct(node.right)
    assert positions.keys().isdisjoint(other_positions)
    return left + right, positions | other_positions


tree = ast.parse(expression.replace("<<<", "<<"), mode="eval")
packed, offsets = reconstruct(tree.body)
ordered = sorted(offsets, key=offsets.get)
assert len(ordered) == 768 and offsets[ordered[0]] == 0
widths = {}
for i, name in enumerate(ordered):
    if i + 1 < len(ordered):
        width = offsets[ordered[i + 1]] - offsets[name]
    else:
        width = len(dict(records)[name]) * 4
    widths[name] = width
    assert 0 <= values[name] < 1 << width
print("All 768 raw chunks fit their nonoverlapping positions.")

steps = ((1, 0), (0, 1), (-1, 0), (0, -1))


def decode(code):
    return tuple((code // 4**i) % 4 for i in range(9, -1, -1))


def raw_window(directions):
    position = (0, 0)
    used = set()
    for direction in directions:
        step = steps[direction]
        endpoint = (position[0] + step[0], position[1] + step[1])
        bond = frozenset((position, endpoint))
        if bond in used:
            return False
        used.add(bond)
        position = endpoint
    return True


for index in range(650, 655):
    name = f"rawClass_{index}"
    offset, width = offsets[name], widths[name]
    first, last = offset // 12, (offset + width - 1) // 12
    codes = range(first, last + 1)
    # Include lanes crossing chunk boundaries in the reconstructed table.
    assert {(packed >> (12 * code)) & 4095 for code in codes} == {3741}
    # Also compare every bit of the literal to an independently packed
    # sentinel sequence at the required alignment.
    expected = sum(3741 << (12 * i) for i in range(len(codes)))
    expected = (expected >> (offset - 12 * first)) & ((1 << width) - 1)
    assert values[name] == expected
    assert all(decode(code)[:2] == (0, 2) for code in codes)
    assert all(not raw_window(decode(code)) for code in codes)
    print(
        f"{name}: bits {offset}..{offset + width - 1}; "
        f"codes {first}..{last}; {len(codes)} touched lanes; "
        "all lanes = 3741; all words start E,W; zero raw windows."
    )
print("PASS: all five scoped literals have the required meaning.")
