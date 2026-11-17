"""Exact integer and lattice checks for the five assigned data declarations."""

import ast
import json
import re
from pathlib import Path


SOURCE = Path(
    "/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean"
)
source = SOURCE.read_text()
literals = {
    match[1]: int(match[2], 16)
    for match in re.finditer(
        r"private noncomputable def (\w+) : ℕ := 0x([0-9a-f]+)", source
    )
}
assembly = next(
    line.split(":=", 1)[1].strip()
    for line in source.splitlines()
    if line.startswith("noncomputable def rawClass :")
)
# All shifts in this expression have explicit parentheses. Interpret only
# names, addition and natural-number shifts; no source code is executed.
tree = ast.parse(assembly.replace("<<<", "<<"), mode="eval").body
offsets = {}


def assemble(node, offset=0):
    if isinstance(node, ast.Name):
        assert node.id not in offsets
        offsets[node.id] = offset
        return literals[node.id]
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add):
        return assemble(node.left, offset) + assemble(node.right, offset)
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.LShift):
        assert isinstance(node.right, ast.Constant)
        assert isinstance(node.right.value, int) and node.right.value >= 0
        return assemble(node.left, offset + node.right.value) << node.right.value
    raise ValueError(ast.dump(node))


packed = assemble(tree)
assert set(offsets) == {f"rawClass_{i}" for i in range(768)}


def digits(code):
    return [(code >> shift) & 3 for shift in range(18, -1, -2)]


def is_raw(code):
    vertex = (0, 0)
    bonds = set()
    for direction in digits(code):
        dx, dy = ((1, 0), (0, 1), (-1, 0), (0, -1))[direction]
        endpoint = vertex[0] + dx, vertex[1] + dy
        bond = tuple(sorted((vertex, endpoint)))
        if bond in bonds:
            return False
        bonds.add(bond)
        vertex = endpoint
    return True


results = []
all_codes = set()
for index in range(740, 745):
    name = f"rawClass_{index}"
    offset = offsets[name]
    width = 16384
    assert 0 <= literals[name] < 1 << width
    low, high = offset // 12, (offset + width - 1) // 12

    # Compare every bit of the literal to the appropriately aligned part
    # of a periodic sequence of 12-bit 0xe9d (= 3741) sentinels.
    repeat_count = (width + offset % 12 + 11) // 12
    repeated_sentinel = 3741 * ((1 << (12 * repeat_count)) - 1) // 4095
    expected = (repeated_sentinel >> (offset % 12)) & ((1 << width) - 1)
    assert literals[name] == expected

    codes = range(low, high + 1)
    for code in codes:
        assert ((packed >> (12 * code)) & 4095) == 3741
        assert not is_raw(code)
        word = digits(code)
        # These prefixes give a short mathematical exclusion witness.
        assert word[:3] == [0, 0, 2] or word[:4] == [0, 0, 1, 3]
    all_codes.update(codes)
    results.append(
        {
            "declaration": name,
            "bit_offset": offset,
            "bit_width": width,
            "code_min": low,
            "code_max": high,
            "affected_lanes": high - low + 1,
            "all_literal_bits_match_sentinel": True,
            "all_assembled_lanes_equal_3741": True,
            "raw_windows_in_range": 0,
            "prefixes": sorted(
                {"".join("ENWS"[d] for d in digits(c)[:4]) for c in codes}
            ),
        }
    )

print(json.dumps({"distinct_codes_checked": len(all_codes), "results": results}, indent=2))
