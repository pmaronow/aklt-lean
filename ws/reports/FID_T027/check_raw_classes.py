"""Reproduce the finite literal/offset checks for FID_T027.

Reads only the supplied Lean source. No archive or generator is consulted.
"""

from collections import Counter
from pathlib import Path
import re


SOURCE = Path(
    "/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean"
)
source = SOURCE.read_text()
literals = {
    match[1]: int(match[2], 16)
    for match in re.finditer(
        r"^private noncomputable def (\w+) : ℕ := 0x([0-9a-f]+)$",
        source,
        re.MULTILINE,
    )
}


def parse_packing(name):
    """Parse the fully parenthesized Lean additions/shifts without eval."""
    expression = re.search(
        rf"^noncomputable def {name} : ℕ := (.*)$", source, re.MULTILINE
    )[1]
    tokens = re.findall(r"\w+|<<<|[()+]", expression)
    assert "".join(tokens) == re.sub(r"\s", "", expression)
    position = 0

    def parse():
        nonlocal position
        token = tokens[position]
        position += 1
        if token != "(":
            assert token in literals
            return ("literal", token)
        left = parse()
        operation = tokens[position]
        position += 1
        if operation == "<<<":
            right = int(tokens[position])
            position += 1
        else:
            assert operation == "+"
            right = parse()
        assert tokens[position] == ")"
        position += 1
        return (operation, left, right)

    tree = parse()
    assert position == len(tokens)
    pieces = []

    def evaluate(node, shift=0):
        if node[0] == "literal":
            pieces.append((node[1], shift))
            return literals[node[1]] << shift
        if node[0] == "<<<":
            return evaluate(node[1], shift + node[2])
        assert node[0] == "+"
        return evaluate(node[1], shift) + evaluate(node[2], shift)

    packed = evaluate(tree)
    return packed, pieces


packed, pieces = parse_packing("rawClass")
assert Counter(name for name, _ in pieces) == Counter(
    f"rawClass_{i}" for i in range(768)
)
offsets = dict(pieces)
ordered = sorted(pieces, key=lambda item: item[1])
assert ordered[0][1] == 0
for (name, offset), (_, next_offset) in zip(ordered, ordered[1:]):
    assert literals[name] < 1 << (next_offset - offset)

# Read and parse the remaining packed data in the same file for context.
for name, count in (("representatives", 5), ("destinations", 11), ("edgeKinds", 2)):
    _, other_pieces = parse_packing(name)
    assert Counter(piece for piece, _ in other_pieces) == Counter(
        f"{name}_{i}" for i in range(count)
    )

sentinel = 3741
assert sentinel == 0xE9D and sentinel < 2**12
all_codes = set()
print("declaration line bit_offset code_min code_max lane_count")
for index in range(100, 105):
    name = f"rawClass_{index}"
    offset = offsets[name]
    width = offsets[f"rawClass_{index - 1}"] - offset
    assert width == 16384
    first = offset // 12
    last = (offset + width - 1) // 12
    assert 0 <= first <= last < 4**10

    # Match the entire literal, including its portions of boundary lanes.
    periodic = sum(sentinel << (12 * j) for j in range(1367))
    expected = (periodic >> (offset % 12)) & ((1 << width) - 1)
    assert literals[name] == expected

    for code in range(first, last + 1):
        # Full lanes include any bits supplied by neighbouring chunks.
        assert (packed >> (12 * code)) & 4095 == sentinel
        digits = [(code // (4 ** (9 - j))) % 4 for j in range(10)]
        assert sum(d * 4 ** (9 - j) for j, d in enumerate(digits)) == code
        assert digits[:2] == [3, 1]  # South, then North.

        # The paper's path and the Lean wordBond have equal first two bonds.
        steps = [(1, 0), (0, 1), (-1, 0), (0, -1)]
        vertices = [(0, 0)]
        for digit in digits:
            x, y = vertices[-1]
            dx, dy = steps[digit]
            vertices.append((x + dx, y + dy))
        assert frozenset(vertices[:2]) == frozenset(vertices[1:3])
        all_codes.add(code)

    declaration = re.search(rf"^private noncomputable def {name}\b", source, re.MULTILINE)
    line = source[:declaration.start()].count("\n") + 1
    print(name, line, offset, first, last, last - first + 1)

assert len(all_codes) == 6828
print("PASS: 5 literals; 6828 distinct affected lanes; all sentinel; all non-raw.")
