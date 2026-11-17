"""Read-only audit of the five assigned packed-table pieces.

Run with Python 3; reads only the supplied Lean data file.
"""
from pathlib import Path
import ast
import collections
import json
import re

SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
text = SOURCE.read_text()
pieces = {
    name: (int(digits, 16), len(digits) * 4)
    for name, digits in re.findall(
        r'^private noncomputable def (\w+) : ℕ := 0x([0-9a-f]+)$',
        text, re.MULTILINE)
}
assert len(pieces) == 786
expression = re.search(r'^noncomputable def rawClass : ℕ := (.*)$', text, re.MULTILINE)[1]
tree = ast.parse(expression.replace('<<<', '<<'), mode='eval').body


def unpack_expression(node, offset=0):
    """Flatten the actual shift/add expression; do not assume chunk order."""
    if isinstance(node, ast.Name):
        value, width = pieces[node.id]
        return value << offset, [(offset, offset + width, node.id)]
    assert isinstance(node, ast.BinOp)
    if isinstance(node.op, ast.LShift):
        assert isinstance(node.right, ast.Constant)
        return unpack_expression(node.left, offset + node.right.value)
    assert isinstance(node.op, ast.Add)
    left_value, left_ranges = unpack_expression(node.left, offset)
    right_value, right_ranges = unpack_expression(node.right, offset)
    return left_value + right_value, left_ranges + right_ranges


packed, ranges = unpack_expression(tree)
ranges.sort()
assert len(ranges) == 768
assert ranges[0][0] == 0
assert all(a[1] == b[0] for a, b in zip(ranges, ranges[1:]))
assert ranges[-1][1] == 12 * 4**10 - 4
# The omitted top nibble is zero, not a missing table lane.
assert packed < 2 ** (12 * 4**10)
hex_table = format(packed, f'0{3 * 4**10}x')
classes = [int(hex_table[j:j + 3], 16)
           for j in range(len(hex_table) - 3, -1, -3)]
assert len(classes) == 4**10

STEPS = ((1, 0), (0, 1), (-1, 0), (0, -1))


def directions(code):
    return [(code // 4**(9 - i)) % 4 for i in range(10)]


def repeated_bond(code):
    position = (0, 0)
    seen = {}
    ds = directions(code)
    for i, direction in enumerate(ds):
        dx, dy = STEPS[direction]
        following = position[0] + dx, position[1] + dy
        bond = frozenset((position, following))
        if bond in seen:
            return seen[bond], i
        seen[bond] = i
        position = following
    return None


def common_prefix(words):
    result = words[0].copy()
    for word in words[1:]:
        while result != word[:len(result)]:
            result.pop()
    return result


results = []
for n in range(545, 550):
    name = f'rawClass_{n}'
    low, high, _ = next(r for r in ranges if r[2] == name)
    value, width = pieces[name]
    assert width == 16384
    # Every bit of the literal must match the appropriately aligned sentinel
    # pattern, including the partial lanes crossing its endpoints.
    expected = 0
    for code in range(low // 12, (high - 1) // 12 + 1):
        lane_offset = 12 * code - low
        expected |= (3741 << lane_offset) if lane_offset >= 0 else (3741 >> -lane_offset)
    expected &= (1 << width) - 1
    assert value == expected
    affected = range(low // 12, (high - 1) // 12 + 1)
    assert all(classes[code] == 3741 for code in affected)
    repeats = [repeated_bond(code) for code in affected]
    assert all(repeat is not None for repeat in repeats)
    reversals = collections.Counter(
        next(i for i in range(9) if (ds[i] + 2) % 4 == ds[i + 1])
        for ds in map(directions, affected))
    results.append({
        'declaration': name,
        'bit_interval_half_open': [low, high],
        'affected_codes_inclusive': [affected.start, affected.stop - 1],
        'affected_code_count': len(affected),
        'common_direction_prefix': common_prefix(list(map(directions, affected))),
        'all_affected_lanes': 3741,
        'reversal_positions_zero_based': dict(reversals),
    })

# Independent generation of the raw domain confirms the meaning of the whole
# table's invalid-word sentinel and its coding/alignment. No archived map or
# executable outside the allowed inputs is consulted.
raw_codes = set()
counts = collections.Counter()


def generate(code, position, used, depth):
    counts[depth] += 1
    if depth == 10:
        raw_codes.add(code)
        return
    for d, (dx, dy) in enumerate(STEPS):
        following = position[0] + dx, position[1] + dy
        bond = frozenset((position, following))
        if bond not in used:
            used.add(bond)
            generate(4 * code + d, following, used, depth + 1)
            used.remove(bond)


generate(0, (0, 0), set(), 0)
assert len(raw_codes) == 60092
assert all(0 <= cls <= 3741 and ((cls < 3741) == (code in raw_codes))
           for code, cls in enumerate(classes))
print(json.dumps({
    'literal_definitions_read': len(pieces),
    'raw_chunks_checked_for_nonoverlapping_assembly': len(ranges),
    'raw_counts_by_length': dict(sorted(counts.items())),
    'whole_table_domain_coverage': 'PASS',
    'assigned_pieces': results,
}, indent=2))
