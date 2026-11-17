"""Read-only arithmetic and raw-bond audit for the five assigned chunks."""

import ast
from collections import Counter
from pathlib import Path
import re


SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
text = SOURCE.read_text()
chunks = {}
widths = {}
lines = {}
for line_number, line in enumerate(text.splitlines(), 1):
    match = re.fullmatch(
        r'private noncomputable def rawClass_(\d+) : ℕ := 0x([0-9a-f]+)', line
    )
    if match:
        index = int(match[1])
        assert index not in chunks
        chunks[index] = int(match[2], 16)
        widths[index] = 4 * len(match[2])
        lines[index] = line_number
assert set(chunks) == set(range(768))
assert all(value < 2**16384 for value in chunks.values())

expression = re.search(r'^noncomputable def rawClass : ℕ := (.+)$', text, re.M)[1]
tree = ast.parse(expression.replace('<<<', '<<'), mode='eval').body


def assemble(node):
    """Evaluate only names, addition, and constant shifts; track every offset."""
    if isinstance(node, ast.Name):
        assert re.fullmatch(r'rawClass_\d+', node.id)
        index = int(node.id.removeprefix('rawClass_'))
        return chunks[index], [(index, 0)]
    assert isinstance(node, ast.BinOp)
    left, layout_left = assemble(node.left)
    if isinstance(node.op, ast.LShift):
        assert isinstance(node.right, ast.Constant)
        shift = node.right.value
        assert type(shift) is int and shift >= 0
        return left << shift, [(index, offset + shift) for index, offset in layout_left]
    assert isinstance(node.op, ast.Add)
    right, layout_right = assemble(node.right)
    # In addition to the layout check below, rule out carries in the actual data.
    assert left & right == 0
    return left + right, layout_left + layout_right


packed, layout = assemble(tree)
assert len(layout) == 768
offsets = dict(layout)
assert len(offsets) == 768
assert all(widths[index] == (16380 if index == 767 else 16384) for index in range(768))
assert all(offsets[index] == sum(widths[j] for j in range(index + 1, 768)) for index in range(768))
assert packed < 2 ** (12 * 4**10)

STEPS = ((1, 0), (0, 1), (-1, 0), (0, -1))
NAMES = 'ENWS'


def decode(code):
    return tuple(code // 4 ** (9 - index) % 4 for index in range(10))


def repeated_bond(code):
    position = (0, 0)
    used = {}
    for index, direction in enumerate(decode(code)):
        step = STEPS[direction]
        target = (position[0] + step[0], position[1] + step[1])
        bond = frozenset((position, target))
        assert len(bond) == 2
        if bond in used:
            return used[bond], index
        used[bond] = index
        position = target
    return None


print('Parsed all 768 raw literal chunks and the complete rawClass assembly.')
print('Every chunk fits its declared hexadecimal width; assembly has disjoint fields and no carries.')
print('The final chunk has 16380 bits of storage; the other 767 have 16384 bits.')
union = set()
for index in range(550, 555):
    offset = offsets[index]
    first_code = offset // 12
    last_code = (offset + 16383) // 12
    codes = range(first_code, last_code + 1)
    union.update(codes)

    # The intended value at every intersected code is the invalid-word sentinel.
    # Compare ALL 16384 bits, including the partial lanes at either end.
    phase = offset % 12
    repetitions = (phase + 16384 + 11) // 12
    repeated_sentinel = sum(3741 << (12 * j) for j in range(repetitions))
    expected_chunk = (repeated_sentinel >> phase) & ((1 << 16384) - 1)
    assert chunks[index] == expected_chunk

    lane_values = Counter((packed >> (12 * code)) % 4096 for code in codes)
    assert lane_values == Counter({3741: len(codes)})
    repeats = Counter(repeated_bond(code) for code in codes)
    assert None not in repeats
    prefixes = Counter(''.join(NAMES[d] for d in decode(code)[:4]) for code in codes)
    print(
        f'rawClass_{index}, line {lines[index]}: offset={offset}, phase={phase}, '
        f'codes={first_code}..{last_code}, count={len(codes)}, '
        f'prefixes={dict(prefixes)}, repeated bond indices={dict(repeats)}, '
        f'lane values={dict(lane_values)}, exact chunk comparison=PASS'
    )

assert len(union) == 6828
assert min(union) == 290815 and max(union) == 297642
print(f'PASS: all {len(union)} distinct intersected words are invalid; all five chunks agree bit for bit.')
