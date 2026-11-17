"""Read-only arithmetic check of the five reviewed Automaton10Data chunks.

This checks their full bit contents, their positions in the Lean assembly,
and all affected word lanes (including lanes crossing chunk boundaries).
It is an independent Python check, not a Lean proof.
"""

import ast
import json
import re
from pathlib import Path


SOURCE = Path(
    "/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean"
)
source = SOURCE.read_text()
chunks = {
    name: int(digits, 16)
    for name, digits in re.findall(
        r"private noncomputable def (rawClass_\d+) : ℕ := 0x([0-9a-f]+)",
        source,
    )
}
assembly = next(
    line.split(":=", 1)[1].strip()
    for line in source.splitlines()
    if line.startswith("noncomputable def rawClass :")
)
tree = ast.parse(assembly.replace("<<<", "<<"), mode="eval").body
offsets = {}


def inspect(node, offset=0):
    if isinstance(node, ast.Name):
        assert node.id in chunks and node.id not in offsets
        offsets[node.id] = offset
        return chunks[node.id]
    assert isinstance(node, ast.BinOp)
    if isinstance(node.op, ast.Add):
        return inspect(node.left, offset) + inspect(node.right, offset)
    assert isinstance(node.op, ast.LShift)
    assert isinstance(node.right, ast.Constant)
    shift = node.right.value
    assert isinstance(shift, int) and shift >= 0
    return inspect(node.left, offset + shift) << shift


packed = inspect(tree)
assert len(chunks) == len(offsets) == 768
assert list(offsets) == [f"rawClass_{j}" for j in range(768)]
assert offsets["rawClass_767"] == 0
assert all(
    offsets[f"rawClass_{j}"] == (767 - j) * 16384 - 4
    for j in range(767)
)

# Check every literal fits its disjoint allocated span, excluding arithmetic
# carries between chunks as an explanation of the extracted contents.
end = 0
for name, offset in sorted(offsets.items(), key=lambda item: item[1]):
    assert offset == end
    width = 16380 if name == "rawClass_767" else 16384
    assert 0 <= chunks[name] < 1 << width
    end = offset + width
assert end == 12 * 4**10 - 4
packed_bytes = packed.to_bytes((end + 7) // 8, "little")


def lane(code):
    bit = 12 * code
    byte, shift = divmod(bit, 8)
    return (int.from_bytes(packed_bytes[byte : byte + 3], "little") >> shift) & 4095


def word(code):
    return tuple((code >> (2 * i)) & 3 for i in range(9, -1, -1))


def repeated_bond(w):
    steps = ((1, 0), (0, 1), (-1, 0), (0, -1))
    x = (0, 0)
    seen = {}
    for i, d in enumerate(w):
        dx, dy = steps[d]
        y = (x[0] + dx, x[1] + dy)
        bond = frozenset((x, y))
        if bond in seen:
            return seen[bond], i
        seen[bond] = i
        x = y
    return None


all_codes = set()
for j in range(485, 490):
    name = f"rawClass_{j}"
    low = offsets[name]
    high = low + 16384 - 1
    first, last = low // 12, high // 12
    count = last - first + 1

    # Slice the infinite 12-bit repetition of the invalid-code sentinel.
    repeated = 3741 * ((1 << (12 * count)) - 1) // ((1 << 12) - 1)
    expected = (repeated >> (low % 12)) & ((1 << 16384) - 1)
    assert chunks[name] == expected

    for code in range(first, last + 1):
        assert word(code)[:3] == (1, 1, 3)  # N,N,S
        assert repeated_bond(word(code)) == (1, 2)
        assert lane(code) == 3741
        all_codes.add(code)

    print(
        json.dumps(
            {
                "declaration": name,
                "source_line": 15 + 2 * j,
                "first_bit": low,
                "last_bit": high,
                "first_touched_code": first,
                "last_touched_code": last,
                "touched_lanes": count,
                "all_lanes_equal": 3741,
                "all_words_begin": "NNS",
                "repeated_bond_indices_zero_based": [1, 2],
                "result": "PASS",
            }
        )
    )

assert len(all_codes) == 6827
print(f"PASS: all 81920 reviewed bits and {len(all_codes)} affected word lanes checked.")
