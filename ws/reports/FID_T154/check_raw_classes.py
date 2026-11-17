"""Read-only arithmetic check for the five assigned packed-data declarations."""

from pathlib import Path
import re


SOURCE = Path(
    "/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean"
)
source = SOURCE.read_text()
hexes = dict(re.findall(r"(rawClass_\d+) : ℕ := 0x([0-9a-f]+)", source))
expression = next(
    line.split(":=", 1)[1].strip()
    for line in source.splitlines()
    if line.startswith("noncomputable def rawClass :")
)
tokens = re.findall(r"rawClass_\d+|<<<|\d+|[()+]", expression)
assert "".join(tokens) == re.sub(r"\s+", "", expression)
position = 0


def atom():
    global position
    token = tokens[position]
    position += 1
    if token == "(":
        result = parse()
        assert tokens[position] == ")"
        position += 1
        return result
    assert token in hexes
    return {token: 0}


def parse():
    global position
    result = atom()
    while position < len(tokens) and tokens[position] != ")":
        operator = tokens[position]
        position += 1
        if operator == "<<<":
            shift = int(tokens[position])
            position += 1
            result = {name: offset + shift for name, offset in result.items()}
        else:
            assert operator == "+"
            other = atom()
            assert not result.keys() & other.keys()
            result.update(other)
    return result


offsets = parse()
assert position == len(tokens)
assert set(offsets) == set(hexes) == {f"rawClass_{i}" for i in range(768)}
ordered = sorted(offsets, key=offsets.get)
assert offsets[ordered[0]] == 0
for lower, upper in zip(ordered, ordered[1:]):
    assert offsets[lower] + 4 * len(hexes[lower]) == offsets[upper]
assert ordered == [f"rawClass_{i}" for i in reversed(range(768))]

# The final chunk has 4095 hex digits; all earlier chunks have 4096.
# The explicit shifts account for this, so use the actual expression offsets.
packed_hex = "".join(hexes[f"rawClass_{i}"] for i in range(768))
assert len(packed_hex) == 3 * 4**10 - 1
packed_hex = packed_hex.rjust(3 * 4**10, "0")


def raw_class_at(code):
    end = len(packed_hex) - 3 * code
    return int(packed_hex[end - 3 : end], 16)


def directions(code):
    return tuple((code // 4 ** (9 - i)) % 4 for i in range(10))


def raw_window(code):
    steps = ((1, 0), (0, 1), (-1, 0), (0, -1))
    x = y = 0
    bonds = set()
    for direction in directions(code):
        dx, dy = steps[direction]
        next_x, next_y = x + dx, y + dy
        bond = tuple(sorted(((x, y), (next_x, next_y))))
        if bond in bonds:
            return False
        bonds.add(bond)
        x, y = next_x, next_y
    return True


affected = set()
for index in range(735, 740):
    name = f"rawClass_{index}"
    offset = offsets[name]
    assert len(hexes[name]) == 4096
    expected = sum(
        ((3741 >> ((offset + bit) % 12)) & 1) << bit
        for bit in range(16384)
    )
    assert int(hexes[name], 16) == expected
    first, last = offset // 12, (offset + 16383) // 12
    for code in range(first, last + 1):
        assert raw_class_at(code) == 3741
        assert directions(code)[:3] == (0, 0, 2)
        assert not raw_window(code)
        affected.add(code)
    print(
        f"{name}: PASS; bits {offset}..{offset + 16383}; "
        f"codes {first}..{last}; {last - first + 1} lanes"
    )

assert affected == set(range(38229, 45056))
print(f"PASS: all {len(affected)} affected codes are invalid and have sentinel 3741")
