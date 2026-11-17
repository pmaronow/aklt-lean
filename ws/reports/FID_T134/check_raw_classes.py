"""Reproduce the finite literal checks for FID_T134 (no Lean process needed)."""

import ast
from pathlib import Path
import re


SOURCE = Path(
    "/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean"
)
text = SOURCE.read_text()
literals = {
    match[1]: int(match[2], 16)
    for match in re.finditer(
        r"private noncomputable def (\w+) : ℕ := (0x[0-9a-f]+)", text
    )
}
expression = re.search(
    r"^noncomputable def rawClass : ℕ := (.*)$", text, re.M
)[1]
tree = ast.parse(expression.replace("<<<", "<<"), mode="eval").body


def evaluate(node):
    if isinstance(node, ast.Constant) and type(node.value) is int:
        return node.value
    if isinstance(node, ast.Name):
        return literals[node.id]
    assert isinstance(node, ast.BinOp)
    if isinstance(node.op, ast.Add):
        return evaluate(node.left) + evaluate(node.right)
    assert isinstance(node.op, ast.LShift)
    return evaluate(node.left) << evaluate(node.right)


def contributions(node, offset=0):
    if isinstance(node, ast.Name):
        return [(node.id, offset)]
    assert isinstance(node, ast.BinOp)
    if isinstance(node.op, ast.Add):
        return contributions(node.left, offset) + contributions(node.right, offset)
    assert isinstance(node.op, ast.LShift)
    assert isinstance(node.right, ast.Constant)
    return contributions(node.left, offset + node.right.value)


parts = contributions(tree)
assert [name for name, _ in parts] == [f"rawClass_{i}" for i in range(768)]
offsets = dict(parts)
previous_end = 0
for name, offset in reversed(parts):
    assert offset == previous_end
    width = 16380 if name == "rawClass_767" else 16384
    assert 0 <= literals[name] < 1 << width
    previous_end = offset + width
assert previous_end == 12 * 4**10 - 4
packed = evaluate(tree)
# Leading zero padding restores the full 4^10 lanes, each three hex digits.
hex_table = f"{packed:0{3 * 4**10}x}"


def lane(code):
    start = 3 * (4**10 - 1 - code)
    return int(hex_table[start : start + 3], 16)


def decode(code):
    return [(code // 4**i) % 4 for i in reversed(range(10))]


STEPS = [(1, 0), (0, 1), (-1, 0), (0, -1)]


def raw_window(word):
    position = (0, 0)
    used = set()
    for d in word:
        step = STEPS[d]
        next_position = (position[0] + step[0], position[1] + step[1])
        bond = frozenset((position, next_position))
        if bond in used:
            return False
        used.add(bond)
        position = next_position
    return True


touched = set()
print("All 768 rawClass chunks are contiguous, bounded, and free of carries.")
for index in range(635, 640):
    name = f"rawClass_{index}"
    offset = offsets[name]
    width = 16384
    low = offset // 12
    high = (offset + width - 1) // 12
    codes = range(low, high + 1)
    expected_lanes = sum(3741 << (12 * j) for j in range(len(codes)))
    expected_chunk = (expected_lanes >> (offset % 12)) & ((1 << width) - 1)
    assert literals[name] == expected_chunk
    assert ((packed >> offset) & ((1 << width) - 1)) == literals[name]
    for code in codes:
        word = decode(code)
        assert word[:2] == [0, 2]
        assert not raw_window(word)
        assert lane(code) == 3741
        touched.add(code)
    print(
        f"{name}: PASS; offset={offset}; codes={low}..{high}; "
        f"intersecting lanes={len(codes)}; every lane=3741; "
        "every word starts E,W and repeats its first bond."
    )
assert len(touched) == 6827
print(f"Distinct affected word codes: {len(touched)}. All checks passed.")
