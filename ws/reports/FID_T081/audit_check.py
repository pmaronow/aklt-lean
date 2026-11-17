"""Check the five assigned packed-table fragments using only the supplied Lean source."""

import ast
from pathlib import Path
import re

SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
source = SOURCE.read_text()
literals = {}
for name, digits in re.findall(
    r'^private noncomputable def (\w+) : ℕ := 0x([0-9a-f]+)$', source, re.M
):
    assert name not in literals
    literals[name] = (int(digits, 16), 4 * len(digits))

expression = re.search(r'^noncomputable def rawClass : ℕ := (.+)$', source, re.M)[1]
tree = ast.parse(expression.replace('<<<', '<<'), mode='eval').body
leaves = []


def inspect(node, offset=0):
    if isinstance(node, ast.Name):
        assert re.fullmatch(r'rawClass_\d+', node.id)
        value, width = literals[node.id]
        leaves.append((offset, width, node.id))
        return value
    assert isinstance(node, ast.BinOp)
    if isinstance(node.op, ast.Add):
        return inspect(node.left, offset) + inspect(node.right, offset)
    assert isinstance(node.op, ast.LShift)
    assert isinstance(node.right, ast.Constant)
    shift = node.right.value
    assert isinstance(shift, int) and shift >= 0
    return inspect(node.left, offset + shift) << shift


packed = inspect(tree)
assert {name for _, _, name in leaves} == {f'rawClass_{i}' for i in range(768)}
assert len(leaves) == 768
cursor = 0
for offset, width, name in sorted(leaves):
    assert offset == cursor, (name, offset, cursor)
    assert literals[name][0].bit_length() <= width
    cursor += width
assert cursor == 12 * 4**10 - 4
assert packed.bit_length() <= 12 * 4**10
print('Parsed all 786 hexadecimal literals and the complete rawClass expression.')
assert len(literals) == 786
print('All 768 rawClass fragments have disjoint, contiguous bit allocations; no carries.')

offsets = {name: (offset, width) for offset, width, name in leaves}
all_codes = set()
steps = ((1, 0), (0, 1), (-1, 0), (0, -1))
for i in range(370, 375):
    name = f'rawClass_{i}'
    offset, width = offsets[name]
    assert width == 16384
    lo, hi = offset // 12, (offset + width - 1) // 12
    lane_count = (offset % 12 + width + 11) // 12
    sentinel_run = 3741 * ((1 << (12 * lane_count)) - 1) // ((1 << 12) - 1)
    expected = (sentinel_run >> (offset % 12)) & ((1 << width) - 1)
    assert literals[name][0] == expected, name
    for code in range(lo, hi + 1):
        all_codes.add(code)
        assert 0 <= code < 4**10
        digits = tuple((code // 4**(9-j)) % 4 for j in range(10))
        assert sum(d * 4**(9-j) for j, d in enumerate(digits)) == code
        assert digits[:2] == (2, 0)
        z0 = (0, 0)
        z1 = steps[digits[0]]
        z2 = tuple(a + b for a, b in zip(z1, steps[digits[1]]))
        assert z2 == z0
        assert frozenset((z0, z1)) == frozenset((z1, z2))
        assert ((packed >> (12 * code)) & 4095) == 3741
    print(f'{name}: offset={offset}; width={width}; offset mod 12={offset % 12}; '
          f'touched codes={lo}..{hi} ({hi-lo+1}); all invalid; all lanes=3741')

assert min(all_codes) == 536575 and max(all_codes) == 543402
assert len(all_codes) == 6828
print('PASS: exact sentinel bits and complete boundary lanes checked for all 6828 affected codes.')
