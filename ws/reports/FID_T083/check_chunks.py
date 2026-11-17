"""Check the five assigned packed class-map fragments against raw windows.

Reads only the supplied Lean source. Uses Python exact integers; no Lean process.
"""

import ast
import json
import re
from pathlib import Path


SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
source = SOURCE.read_text()
literals = {
    name: int(digits, 16)
    for name, digits in re.findall(
        r'private noncomputable def (\w+) : ℕ := 0x([0-9a-f]+)', source
    )
}


def unpack_expression(name):
    line = next(s for s in source.splitlines() if s.startswith(f'noncomputable def {name} :'))
    expression = ast.parse(line.split(':=', 1)[1].strip().replace('<<<', '<<'), mode='eval').body

    def walk(node, offset=0):
        if isinstance(node, ast.Name):
            return [(node.id, offset)]
        assert isinstance(node, ast.BinOp)
        if isinstance(node.op, ast.Add):
            return walk(node.left, offset) + walk(node.right, offset)
        assert isinstance(node.op, ast.LShift)
        assert isinstance(node.right, ast.Constant) and isinstance(node.right.value, int)
        return walk(node.left, offset + node.right.value)

    pieces = walk(expression)
    by_offset = sorted(pieces, key=lambda p: p[1])
    assert len(set(n for n, _ in pieces)) == len(pieces)
    assert by_offset[0][1] == 0
    # Each lower block fits before the next: addition cannot carry across blocks.
    for (name, offset), (_, next_offset) in zip(by_offset, by_offset[1:]):
        assert literals[name] < 1 << (next_offset - offset)
    packed = sum(literals[n] << offset for n, offset in pieces)
    return dict(pieces), packed


offsets, packed = unpack_expression('rawClass')
assert len(offsets) == 768
assert set(offsets) == {f'rawClass_{j}' for j in range(768)}
packed_bytes = packed.to_bytes(12 * 4**10 // 8, 'little')


def class_at(code):
    bit = 12 * code
    byte, intra = divmod(bit, 8)
    return (int.from_bytes(packed_bytes[byte:byte + 3], 'little') >> intra) & 4095


def directions(code):
    return tuple((code // 4**i) % 4 for i in reversed(range(10)))


STEPS = ((1, 0), (0, 1), (-1, 0), (0, -1))


def raw_window(word):
    x = y = 0
    bonds = set()
    for d in word:
        dx, dy = STEPS[d]
        nx, ny = x + dx, y + dy
        # Finset endpoints implement an unoriented bond.
        bond = frozenset(((x, y), (nx, ny)))
        if bond in bonds:
            return False
        bonds.add(bond)
        x, y = nx, ny
    return True


results = []
for j in range(380, 385):
    name = f'rawClass_{j}'
    offset = offsets[name]
    width = 16384
    assert literals[name] < 1 << width
    first = offset // 12
    last = (offset + width - 1) // 12
    codes = range(first, last + 1)
    # Compare every bit, including both possible partial boundary lanes.
    phase = offset % 12
    count = (phase + width + 11) // 12
    sentinels = 3741 * ((1 << (12 * count)) - 1) // ((1 << 12) - 1)
    assert literals[name] == (sentinels >> phase) & ((1 << width) - 1)
    assert all(class_at(c) == 3741 for c in codes)
    assert all(not raw_window(directions(c)) for c in codes)
    assert all(directions(c)[:2] in ((1, 3), (2, 0)) for c in codes)
    results.append({
        'declaration': name,
        'source_line': 15 + 2*j,
        'bit_offset': offset,
        'bit_width': width,
        'offset_mod_12': phase,
        'first_affected_code': first,
        'last_affected_code': last,
        'affected_lanes': len(codes),
        'first_two_directions': sorted({directions(c)[:2] for c in codes}),
        'all_fragments_equal_sentinel': True,
        'all_affected_lanes_equal_3741': True,
        'raw_windows_in_affected_lanes': 0,
    })

print(json.dumps(results, indent=2))
