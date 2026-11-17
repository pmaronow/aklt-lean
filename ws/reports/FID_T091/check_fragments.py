"""Check the five assigned literal fragments against the paper's raw-word domain."""

from pathlib import Path
import re


SOURCE = Path(
    "/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean"
)
text = SOURCE.read_text()
literals = {
    name: int(digits, 16)
    for name, digits in re.findall(
        r"private noncomputable def (\w+) : ℕ := 0x([0-9a-f]+)", text
    )
}
expression = re.search(
    r"^noncomputable def rawClass : ℕ := (.*)$", text, re.MULTILINE
).group(1)
tokens = re.findall(r"rawClass_\d+|<<<|\+|\(|\)|\d+", expression)
assert "".join(tokens) == re.sub(r"\s+", "", expression)
cursor = 0


def parse():
    """The source explicitly parenthesizes every binary operation."""
    global cursor
    token = tokens[cursor]
    cursor += 1
    if token == "(":
        left = parse()
        if tokens[cursor] == ")":
            cursor += 1
            return left
        operator = tokens[cursor]
        cursor += 1
        assert operator in ("+", "<<<")
        right = parse()
        assert tokens[cursor] == ")"
        cursor += 1
        return operator, left, right
    return int(token) if token.isdigit() else token


tree = parse()
assert cursor == len(tokens)
offsets = {}


def assemble(node, offset=0):
    if isinstance(node, str):
        assert node not in offsets
        offsets[node] = offset
        return literals[node] << offset
    operator, left, right = node
    if operator == "<<<":
        assert isinstance(right, int)
        return assemble(left, offset + right)
    return assemble(left, offset) + assemble(right, offset)


packed = assemble(tree)
assert list(offsets) == [f"rawClass_{i}" for i in range(768)]

# Check that addition concatenates the literals without overlaps or carries.
last_end = 0
for name, offset in sorted(offsets.items(), key=lambda pair: pair[1]):
    assert offset >= last_end
    width = 16380 if name == "rawClass_767" else 16384
    assert literals[name] < 1 << width
    last_end = offset + width
assert last_end == 12 * 4**10 - 4  # Four omitted leading zero bits.


def decode(code):
    return [(code // 4 ** (9 - i)) % 4 for i in range(10)]


def raw_window(word):
    position = (0, 0)
    bonds = set()
    for direction in word:
        dx, dy = ((1, 0), (0, 1), (-1, 0), (0, -1))[direction]
        next_position = position[0] + dx, position[1] + dy
        bond = frozenset((position, next_position))
        if bond in bonds:
            return False
        bonds.add(bond)
        position = next_position
    return True


print("Exact natural arithmetic; bit intervals and code ranges are inclusive.")
all_codes = set()
for index in range(420, 425):
    name = f"rawClass_{index}"
    low = offsets[name]
    high = low + 16384 - 1
    first, last = low // 12, high // 12
    mask = (1 << 16384) - 1
    assert ((packed >> low) & mask) == literals[name]

    # Independently construct the expected bits from the invalid-word sentinel.
    expected = 0
    for code in range(first, last + 1):
        word = decode(code)
        assert word[:2] == [1, 3]  # N followed by S reuses the first bond.
        assert not raw_window(word)
        begin, end = max(low, 12 * code), min(high + 1, 12 * (code + 1))
        part = (3741 >> (begin - 12 * code)) & ((1 << (end - begin)) - 1)
        expected |= part << (begin - low)
        all_codes.add(code)
    assert literals[name] == expected

    # Include complete boundary lanes, using neighbouring fragments as needed.
    region = (packed >> (12 * first)) & ((1 << (12 * (last - first + 1))) - 1)
    for code in range(first, last + 1):
        assert ((region >> (12 * (code - first))) & 4095) == 3741
    print(
        f"{name}: PASS; bits {low}..{high}; codes {first}..{last}; "
        f"{last - first + 1} touched lanes; sentinel 3741 throughout"
    )
print(f"Distinct affected word codes: {len(all_codes)}; raw windows: 0.")
