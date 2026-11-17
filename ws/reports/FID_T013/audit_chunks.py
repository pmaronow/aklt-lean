"""Exact integer audit of the five assigned packed-table chunks.

Reads only the supplied Lean input; does not depend on the archived generator.
Run with: python3 audit_chunks.py
"""

from pathlib import Path
import json
import re


SOURCE = Path(
    "/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean"
)
text = SOURCE.read_text()
literals = {
    name: int(value, 16)
    for name, value in re.findall(
        r"^private noncomputable def (\w+) : ℕ := 0x([0-9a-f]+)$",
        text,
        re.MULTILINE,
    )
}
expression = re.search(
    r"^noncomputable def rawClass : ℕ := (.*)$", text, re.MULTILINE
).group(1)
tokens = re.findall(r"rawClass_\d+|\d+|<<<|[()+]", expression)
assert "".join(tokens) == re.sub(r"\s+", "", expression)
position = 0


def atom():
    global position
    token = tokens[position]
    position += 1
    if token == "(":
        result = shift()
        assert tokens[position] == ")"
        position += 1
        return result
    if token.startswith("rawClass_"):
        return {int(token.removeprefix("rawClass_")): 0}
    return int(token)


def add():
    global position
    result = atom()
    while position < len(tokens) and tokens[position] == "+":
        position += 1
        right = atom()
        assert isinstance(result, dict) and isinstance(right, dict)
        assert not result.keys() & right.keys()
        result = result | right
    return result


def shift():
    global position
    result = add()
    while position < len(tokens) and tokens[position] == "<<<":
        position += 1
        amount = add()
        assert isinstance(result, dict) and isinstance(amount, int)
        result = {index: offset + amount for index, offset in result.items()}
    return result


offsets = shift()
assert position == len(tokens)
assert set(offsets) == set(range(768))
for index in range(768):
    width = 16380 if index == 767 else 16384
    expected_offset = 0 if index == 767 else (767 - index) * 16384 - 4
    assert offsets[index] == expected_offset
    assert 0 <= literals[f"rawClass_{index}"] < 1 << width
    if index < 767:
        following_width = 16380 if index == 766 else 16384
        assert offsets[index] == offsets[index + 1] + following_width

# These disjoint bit intervals make the Lean additions exact concatenations.
packed = sum(literals[f"rawClass_{i}"] << offsets[i] for i in range(768))
steps = ((1, 0), (0, 1), (-1, 0), (0, -1))


def digits(code):
    return [(code >> (2 * (9 - i))) & 3 for i in range(10)]


def raw_window(word):
    vertex = (0, 0)
    used = set()
    for direction in word:
        displacement = steps[direction]
        following = tuple(x + y for x, y in zip(vertex, displacement))
        bond = frozenset((vertex, following))
        if bond in used:
            return False
        used.add(bond)
        vertex = following
    return True


results = []
all_affected = set()
for index in range(30, 35):
    offset = offsets[index]
    width = 16384
    first = offset // 12
    last = (offset + width - 1) // 12
    count = last - first + 1
    repeated_sentinel = 3741 * ((1 << (12 * count)) - 1) // ((1 << 12) - 1)
    expected_chunk = (repeated_sentinel >> (offset - 12 * first)) & (
        (1 << width) - 1
    )
    assert literals[f"rawClass_{index}"] == expected_chunk
    for code in range(first, last + 1):
        assert (packed >> (12 * code)) & 4095 == 3741
        word = digits(code)
        assert word[:3] == [3, 3, 1]  # S, S, N: the third step reuses bond 2.
        assert not raw_window(word)
        assert sum(d * 4 ** (9 - i) for i, d in enumerate(word)) == code
        all_affected.add(code)
    results.append(
        {
            "declaration": f"rawClass_{index}",
            "bit_offset": offset,
            "bit_width": width,
            "first_affected_code": first,
            "last_affected_code": last,
            "affected_codes": count,
            "full_literal_equals_sentinel_bits": True,
            "all_affected_lanes_equal_3741": True,
            "raw_windows_in_affected_codes": 0,
        }
    )

print(json.dumps({"chunks": results, "distinct_codes_checked": len(all_affected)}, indent=2))
