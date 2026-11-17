"""Exact, read-only checks of the five assigned packed-data declarations."""

import ast
import json
import re
from pathlib import Path


SOURCE = Path(
    "/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean"
)
text = SOURCE.read_text()
literals = {}
line_numbers = {}
for line_number, line in enumerate(text.splitlines(), 1):
    match = re.fullmatch(
        r"private noncomputable def (\w+) : ℕ := 0x([0-9a-f]+)", line
    )
    if match:
        name, digits = match.groups()
        literals[name] = digits
        line_numbers[name] = line_number


def pieces(node):
    """Flatten the explicitly parenthesized additions and natural left shifts."""
    if isinstance(node, ast.Name):
        return [(node.id, 0)]
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add):
        return pieces(node.left) + pieces(node.right)
    if (
        isinstance(node, ast.BinOp)
        and isinstance(node.op, ast.LShift)
        and isinstance(node.right, ast.Constant)
        and isinstance(node.right.value, int)
        and node.right.value >= 0
    ):
        return [(name, offset + node.right.value) for name, offset in pieces(node.left)]
    raise AssertionError(ast.dump(node))


# Check the entire file's four packed assemblies, including all chunk boundaries.
assemblies = {}
for name in ("rawClass", "representatives", "destinations", "edgeKinds"):
    expression = re.search(
        rf"^noncomputable def {name} : ℕ := (.*)$", text, re.MULTILINE
    ).group(1)
    terms = pieces(ast.parse(expression.replace("<<<", "<<"), mode="eval").body)
    assert len({term[0] for term in terms}) == len(terms)
    intervals = sorted(
        (offset, offset + 4 * len(literals[chunk]), chunk)
        for chunk, offset in terms
    )
    assert intervals[0][0] == 0
    assert all(left[1] == right[0] for left, right in zip(intervals, intervals[1:]))
    assert all(int(literals[chunk], 16) < 2 ** (end - start)
               for start, end, chunk in intervals)
    assemblies[name] = dict(terms)

assert len(assemblies["rawClass"]) == 768
assert set(literals) == set().union(*(set(x) for x in assemblies.values()))
assert list(assemblies["rawClass"]) == [f"rawClass_{i}" for i in range(768)]

# Contiguous disjoint shifts make concatenation exactly the same natural number.
# The omitted high hexadecimal zero is supplied for fixed-width lane indexing.
raw_hex = "".join(literals[f"rawClass_{i}"] for i in range(768)).zfill(3 * 4**10)
assert len(raw_hex) == 3 * 4**10


def raw_class_at(code):
    start = len(raw_hex) - 3 * (code + 1)
    return int(raw_hex[start : start + 3], 16)


results = []
all_affected_codes = set()
for number in range(395, 400):
    name = f"rawClass_{number}"
    digits = literals[name]
    width = 4 * len(digits)
    offset = assemblies["rawClass"][name]
    phase = offset % 12

    # A complete bit-for-bit comparison, with the global 12-bit lane phase.
    lane_count = (width + phase + 11) // 12
    repeated_marker = 3741 * ((2 ** (12 * lane_count) - 1) // (2**12 - 1))
    expected = (repeated_marker >> phase) & (2**width - 1)
    assert int(digits, 16) == expected

    first_code = offset // 12
    last_code = (offset + width - 1) // 12
    for code in range(first_code, last_code + 1):
        # Include both partial boundary lanes and their neighbouring chunks.
        assert raw_class_at(code) == 3741
        # Most-significant-first E,N,W,S coding: every word starts N,S.
        assert code // 4**9 == 1
        assert (code // 4**8) % 4 == 3
        # These first two steps traverse the same unoriented bond twice.
        origin, north = (0, 0), (0, 1)
        assert frozenset((origin, north)) == frozenset((north, origin))
        all_affected_codes.add(code)

    results.append(
        {
            "declaration": name,
            "line": line_numbers[name],
            "hex_digits_checked": len(digits),
            "bit_range_inclusive": [offset, offset + width - 1],
            "code_range_inclusive": [first_code, last_code],
            "lane_value": 3741,
            "word_prefix": "NS",
            "status": "PASS",
        }
    )

print(json.dumps({
    "results": results,
    "distinct_affected_lanes_checked": len(all_affected_codes),
    "all_packed_assemblies_have_disjoint_contiguous_chunks": True,
}, indent=2))
