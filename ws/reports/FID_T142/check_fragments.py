"""Read-only arithmetic audit of the five assigned packed literal fragments."""

from pathlib import Path
import re


SOURCE = Path(
    "/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean"
)
source = SOURCE.read_text()
literals = {}
hex_widths = {}
for line in source.splitlines():
    match = re.fullmatch(
        r"private noncomputable def (\w+) : ℕ := 0x([0-9a-fA-F]+)", line
    )
    if match:
        name, digits = match.groups()
        literals[name] = int(digits, 16)
        hex_widths[name] = 4 * len(digits)


def assemble(name):
    """Evaluate the actual parenthesized Nat expression and track leaf offsets."""
    line = next(
        line for line in source.splitlines()
        if line.startswith(f"noncomputable def {name} : ℕ := ")
    )
    expression = line.split(":=", 1)[1]
    tokens = re.findall(r"\w+|<<<|[()+]", expression)
    assert "".join(tokens) == re.sub(r"\s+", "", expression)
    position = 0

    def parse():
        nonlocal position
        token = tokens[position]
        position += 1
        if token != "(":
            return (int(token), {}) if token.isdigit() else (
                literals[token], {token: 0}
            )
        left, left_offsets = parse()
        operation = tokens[position]
        position += 1
        right, right_offsets = parse()
        assert tokens[position] == ")"
        position += 1
        if operation == "<<<":
            assert not right_offsets
            return left << right, {
                key: offset + right for key, offset in left_offsets.items()
            }
        assert operation == "+"
        assert left_offsets.keys().isdisjoint(right_offsets)
        return left + right, left_offsets | right_offsets

    packed, offsets = parse()
    assert position == len(tokens)
    ordered = sorted((offset, key) for key, offset in offsets.items())
    assert ordered[0][0] == 0
    for (offset, key), (next_offset, _) in zip(ordered, ordered[1:]):
        assert offset + hex_widths[key] == next_offset
        assert literals[key] < 1 << (next_offset - offset)
    return packed, offsets


# Parse all packed tables in the file. In particular, verify that concatenation
# by addition cannot carry between the rawClass fragments.
tables = {name: assemble(name) for name in (
    "rawClass", "representatives", "destinations", "edgeKinds"
)}
packed, offsets = tables["rawClass"]
assert len(offsets) == 768
sentinel = 3741
assert sentinel == 0xE9D < 2**12
periodic = sentinel * ((1 << (12 * 1367)) - 1) // ((1 << 12) - 1)
all_codes = set()

for index in range(675, 680):
    name = f"rawClass_{index}"
    offset = offsets[name]
    width = hex_widths[name]
    assert width == 16384
    mask = (1 << width) - 1
    expected = (periodic >> (offset % 12)) & mask
    assert literals[name] == expected
    assert (packed >> offset) & mask == expected
    first = offset // 12
    last = (offset + width - 1) // 12
    for code in range(first, last + 1):
        directions = [(code // 4**(9 - i)) % 4 for i in range(10)]
        assert directions[:3] == [0, 1, 3]  # E, N, S
        assert (packed >> (12 * code)) & 4095 == sentinel
        x = y = 0
        bonds = []
        for direction in directions:
            dx, dy = [(1, 0), (0, 1), (-1, 0), (0, -1)][direction]
            next_vertex = (x + dx, y + dy)
            bonds.append(frozenset(((x, y), next_vertex)))
            x, y = next_vertex
        assert bonds[1] == bonds[2]
        assert len(set(bonds)) < 10
        all_codes.add(code)
    print(
        f"{name}: bits [{offset}, {offset + width - 1}], "
        f"codes [{first}, {last}]; exact marker pattern and invalidity PASS"
    )

assert len(all_codes) == 6827
assert min(all_codes) == 120149 and max(all_codes) == 126975
print("PASS: all 81,920 assigned bits and 6,827 affected full lanes checked.")
