"""Exact integer check of the five assigned Automaton10Data fragments.

Reads only the supplied Lean data file. No Lean process is launched.
"""

import ast
import json
import re
from pathlib import Path


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
    r"^noncomputable def rawClass : ℕ := (.*)$", text, re.M
).group(1)
offsets = {}


def expand(node, offset=0):
    """Expand the actual parenthesized Lean shift/add tree, preserving precedence."""
    if isinstance(node, ast.Name):
        assert node.id not in offsets
        offsets[node.id] = offset
        return literals[node.id] << offset
    assert isinstance(node, ast.BinOp)
    if isinstance(node.op, ast.LShift):
        assert isinstance(node.right, ast.Constant)
        return expand(node.left, offset + node.right.value)
    assert isinstance(node.op, ast.Add)
    return expand(node.left, offset) + expand(node.right, offset)


packed = expand(ast.parse(expression.replace("<<<", "<<"), mode="eval").body)
assert set(offsets) == {f"rawClass_{i}" for i in range(768)}
spans = sorted(
    (offset, offset + literals[name].bit_length(), name)
    for name, offset in offsets.items()
)
assert all(left[1] <= right[0] for left, right in zip(spans, spans[1:]))

sentinel = 3741
width = 16384
mask = (1 << width) - 1
rows = []
all_codes = set()
for index in range(415, 420):
    name = f"rawClass_{index}"
    offset = offsets[name]
    value = literals[name]
    assert value.bit_length() == width
    # Independent expected bit pattern: every 12-bit lane is the invalid marker.
    expected = sum(
        ((sentinel >> ((offset + bit) % 12)) & 1) << bit
        for bit in range(width)
    )
    assert value == expected
    assert (packed >> offset) & mask == value
    first = offset // 12
    last = (offset + width - 1) // 12
    for code in range(first, last + 1):
        assert 0 <= code < 4**10
        assert (packed >> (12 * code)) & 4095 == sentinel
        # Paper's most-significant-first code: first two directions are N,S.
        assert code // (4**9) % 4 == 1
        assert code // (4**8) % 4 == 3
        directions = [(code // (4 ** (9 - i))) % 4 for i in range(10)]
        steps = [(1, 0), (0, 1), (-1, 0), (0, -1)]
        position = (0, 0)
        bonds = []
        for direction in directions:
            dx, dy = steps[direction]
            following = (position[0] + dx, position[1] + dy)
            bonds.append(frozenset((position, following)))
            position = following
        assert bonds[0] == bonds[1]
        assert len(set(bonds)) < 10
        all_codes.add(code)
    rows.append(
        {
            "declaration": name,
            "source_line": text[: text.index(f"private noncomputable def {name} ")].count("\n") + 1,
            "bit_interval_inclusive": [offset, offset + width - 1],
            "word_code_interval_inclusive": [first, last],
            "touched_lanes": last - first + 1,
            "all_lane_values": sentinel,
            "all_words_start": "NS",
            "exact_fragment_matches_sentinel_pattern": True,
        }
    )

assert len(all_codes) == 6828
assert max(all_codes) - min(all_codes) + 1 == len(all_codes)
print(
    json.dumps(
        {
            "raw_table_chunks": len(offsets),
            "overlapping_chunk_bits": False,
            "results": rows,
            "distinct_affected_words": len(all_codes),
            "all_checks_passed": True,
        },
        indent=2,
    )
)
