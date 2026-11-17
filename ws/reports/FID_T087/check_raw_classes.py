"""Read-only audit of the five assigned packed natural-number fragments."""

import ast
from collections import Counter
from pathlib import Path
import re


SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
text = SOURCE.read_text()
literals = {}
source_lines = {}
widths = {}
for line_number, line in enumerate(text.splitlines(), 1):
    match = re.fullmatch(r'private noncomputable def (\w+) : ℕ := (0x[0-9a-f]+)', line)
    if match:
        name, literal = match.groups()
        literals[name] = int(literal, 16)
        widths[name] = (len(literal) - 2) * 4
        source_lines[name] = line_number


def assembly_offsets(node, offset=0):
    if isinstance(node, ast.Name):
        return [(node.id, offset)]
    assert isinstance(node, ast.BinOp), ast.dump(node)
    if isinstance(node.op, ast.Add):
        return assembly_offsets(node.left, offset) + assembly_offsets(node.right, offset)
    assert isinstance(node.op, ast.LShift), ast.dump(node)
    assert isinstance(node.right, ast.Constant) and isinstance(node.right.value, int)
    return assembly_offsets(node.left, offset + node.right.value)


assembly = re.search(r'^noncomputable def rawClass : ℕ := (.+)$', text, re.M)[1]
tree = ast.parse(assembly.replace('<<<', '<<'), mode='eval')
leaves = assembly_offsets(tree.body)
assert len(leaves) == 768
offsets = dict(leaves)
assert set(offsets) == {f'rawClass_{i}' for i in range(768)}
cursor = 0
packed = 0
for name, offset in sorted(offsets.items(), key=lambda pair: pair[1]):
    assert offset == cursor, (name, offset, cursor)
    assert literals[name] < 2 ** widths[name]
    packed += literals[name] << offset
    cursor += widths[name]
assert cursor == 12 * 4**10 - 4
packed_bytes = packed.to_bytes((12 * 4**10 + 7) // 8, 'little')


def lane(code):
    bit = 12 * code
    return (int.from_bytes(packed_bytes[bit // 8:bit // 8 + 3], 'little') >> (bit % 8)) & 4095


def word(code):
    return [(code // 4**(9 - i)) % 4 for i in range(10)]


def repeated_bond(directions):
    steps = [(1, 0), (0, 1), (-1, 0), (0, -1)]
    position = (0, 0)
    seen = set()
    for d in directions:
        delta = steps[d]
        following = (position[0] + delta[0], position[1] + delta[1])
        bond = frozenset((position, following))
        if bond in seen:
            return True
        seen.add(bond)
        position = following
    return False


print('Parsed all literal definitions and the complete rawClass assembly.')
print('All 768 rawClass fragments occupy disjoint, contiguous bit intervals.')
print('The four omitted highest bits of the full 4^10-lane capacity are zero.')
all_codes = set()
for i in range(400, 405):
    name = f'rawClass_{i}'
    low = offsets[name]
    high = low + widths[name] - 1
    first, last = low // 12, high // 12
    codes = range(first, last + 1)
    all_codes.update(codes)
    values = Counter(lane(code) for code in codes)
    raw_count = sum(not repeated_bond(word(code)) for code in codes)
    prefixes = sorted({''.join('ENWS'[d] for d in word(code)[:3]) for code in codes})
    assert values == {3741: len(codes)}, (name, values)
    assert raw_count == 0, (name, raw_count)
    # Also compare each fragment itself to its exact slice of repeated 12-bit 0xE9D.
    expected = 0
    for code in codes:
        start, end = max(low, 12 * code), min(high + 1, 12 * (code + 1))
        part = (3741 >> (start - 12 * code)) & ((1 << (end - start)) - 1)
        expected |= part << (start - low)
    assert literals[name] == expected, name
    print(f'{name} (Lean line {source_lines[name]}): bits [{low}, {high}], '
          f'codes [{first}, {last}], start residue {low % 12}, '
          f'{len(codes)} affected lanes, values {dict(values)}, '
          f'raw words {raw_count}, three-direction prefixes {prefixes}')

print(f'Union: {min(all_codes)}..{max(all_codes)}, {len(all_codes)} distinct codes; '
      'all have prefix N S W, so bonds 0 and 1 coincide.')
assert all(word(code)[:3] == [1, 3, 2] for code in all_codes)
print('PASS: every assigned fragment is exactly the non-raw sentinel bits required here.')
