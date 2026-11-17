"""Reproduce the integer and raw-word checks for the five assigned fragments."""

from pathlib import Path
import re


SOURCE = Path(
    "/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean"
)
source = SOURCE.read_text()
literals = {
    name: (int(digits, 16), 4 * len(digits))
    for name, digits in re.findall(
        r"^private noncomputable def (\w+) : ℕ := 0x([0-9a-f]+)$",
        source,
        re.MULTILINE,
    )
}


def reconstruct(name):
    expression = re.search(
        rf"^noncomputable def {name} : ℕ := (.*)$", source, re.MULTILINE
    )[1]
    tokens = re.findall(r"\w+|<<<|[()+]", expression)
    assert "".join(tokens) == re.sub(r"\s+", "", expression)
    position = 0

    def atom():
        nonlocal position
        token = tokens[position]
        position += 1
        if token == "(":
            result = expression_node()
            assert tokens[position] == ")"
            position += 1
            return result
        value, width = literals[token]
        assert value < 2**width
        return value, {token: 0}

    def expression_node():
        nonlocal position
        value, offsets = atom()
        operations = 0
        while position < len(tokens) and tokens[position] != ")":
            operation = tokens[position]
            position += 1
            operations += 1
            if operation == "<<<":
                shift = int(tokens[position])
                position += 1
                value <<= shift
                offsets = {key: offset + shift for key, offset in offsets.items()}
            else:
                assert operation == "+"
                other, other_offsets = atom()
                assert value & other == 0, "Addition would introduce a carry"
                assert offsets.keys().isdisjoint(other_offsets)
                value += other
                offsets.update(other_offsets)
        # All source operations are explicitly parenthesized, so parsing does
        # not depend on any assumed relative precedence of + and <<<.
        assert operations <= 1
        return value, offsets

    result = expression_node()
    assert position == len(tokens)
    return result


tables = {}
used_literals = set()
for table_name in ("rawClass", "representatives", "destinations", "edgeKinds"):
    tables[table_name] = reconstruct(table_name)
    used_literals.update(tables[table_name][1])
assert used_literals == literals.keys()

packed, offsets = tables["rawClass"]
packed_bytes = packed.to_bytes((packed.bit_length() + 7) // 8, "little")


def raw_class_at(code):
    byte_index, bit_index = divmod(12 * code, 8)
    return (int.from_bytes(packed_bytes[byte_index : byte_index + 3], "little") >> bit_index) % 4096


def decode(code):
    return [(code // 4 ** (9 - index)) % 4 for index in range(10)]


steps = ((1, 0), (0, 1), (-1, 0), (0, -1))


def first_repeated_bond(word):
    vertex = (0, 0)
    bonds = set()
    for index, direction in enumerate(word):
        dx, dy = steps[direction]
        successor = (vertex[0] + dx, vertex[1] + dy)
        bond = frozenset((vertex, successor))
        if bond in bonds:
            return index
        bonds.add(bond)
        vertex = successor
    return None


affected = set()
print(f"Parsed {len(literals)} literal fragments and all four packed tables; no carries.")
for index in range(640, 645):
    name = f"rawClass_{index}"
    offset = offsets[name]
    value, width = literals[name]
    assert width == 16384
    lower_code = offset // 12
    upper_code = (offset + width - 1) // 12
    # Compare every bit of the fragment to the periodic 12-bit marker.
    expected = sum(
        ((3741 >> ((offset + bit) % 12)) & 1) << bit
        for bit in range(width)
    )
    assert value == expected
    for code in range(lower_code, upper_code + 1):
        assert 0 <= code < 4**10
        assert raw_class_at(code) == 3741  # Includes split boundary lanes.
        word = decode(code)
        assert word[:2] == [0, 2]
        assert sum(d * 4 ** (9 - i) for i, d in enumerate(word)) == code
        assert first_repeated_bond(word) == 1
        affected.add(code)
    print(
        f"{name}: bits [{offset}, {offset + width - 1}], "
        f"codes [{lower_code}, {upper_code}], "
        "every overlapping lane = 3741; every word starts E,W and repeats bond 0."
    )
print(f"PASS: {len(affected)} distinct affected codes checked; no raw windows affected.")
