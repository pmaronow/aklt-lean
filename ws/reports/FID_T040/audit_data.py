"""Read-only arithmetic audit of the assigned Automaton10Data chunks."""

import ast
import json
import re
from array import array
from collections import Counter
from pathlib import Path


SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
TEXT = SOURCE.read_text()
LITERALS = {
    m[1]: int(m[2], 16)
    for m in re.finditer(r'private noncomputable def (\w+) : ℕ := 0x([0-9a-f]+)', TEXT)
}


def assembly(name):
    line = next(s for s in TEXT.splitlines() if s.startswith(f'noncomputable def {name} :'))
    expr = line.split(':= ', 1)[1].replace('<<<', '<<')
    tree = ast.parse(expr, mode='eval').body

    def flatten(node, offset=0):
        if isinstance(node, ast.Name):
            return [(node.id, offset)]
        assert isinstance(node, ast.BinOp)
        if isinstance(node.op, ast.Add):
            return flatten(node.left, offset) + flatten(node.right, offset)
        assert isinstance(node.op, ast.LShift)
        assert isinstance(node.right, ast.Constant)
        return flatten(node.left, offset + node.right.value)

    terms = flatten(tree)
    ordered = sorted(terms, key=lambda item: item[1])
    assert len({key for key, _ in terms}) == len(terms)
    for (key, offset), (_, next_offset) in zip(ordered, ordered[1:]):
        assert LITERALS[key] < 1 << (next_offset - offset), (key, 'overlap')
    packed = sum(LITERALS[key] << offset for key, offset in terms)
    return packed, dict(terms)


def lanes(packed, width, count):
    # Three bytes hold two 12-bit lanes; similarly for widths divisible by four.
    assert width % 4 == 0
    byte_width = width // 4
    data = packed.to_bytes(byte_width * ((count + 1) // 2), 'little')
    mask = (1 << width) - 1
    result = array('I')
    for start in range(0, len(data), byte_width):
        pair = int.from_bytes(data[start:start + byte_width], 'little')
        result.append(pair & mask)
        result.append(pair >> width)
    return result[:count]


PACKED, OFFSETS = assembly('rawClass')
CLASS = lanes(PACKED, 12, 4**10)
assert len(OFFSETS) == 768
assert all(OFFSETS[f'rawClass_{j}'] == (767 - j)*16384 - 4 for j in range(767))
assert OFFSETS['rawClass_767'] == 0
STEPS = ((1, 0), (0, 1), (-1, 0), (0, -1))


def decode(code):
    return tuple((code >> (2*(9 - i))) & 3 for i in range(10))


def first_repeated_bond(code):
    vertex = (0, 0)
    used = {}
    for i, direction in enumerate(decode(code)):
        dx, dy = STEPS[direction]
        end = (vertex[0] + dx, vertex[1] + dy)
        bond = tuple(sorted((vertex, end)))
        if bond in used:
            return used[bond] + 1, i + 1
        used[bond] = i
        vertex = end
    return None


targets = []
for j in range(165, 170):
    name = f'rawClass_{j}'
    offset = OFFSETS[name]
    low, high = offset // 12, (offset + 16383) // 12
    expected = 0
    repeats = Counter()
    for code in range(low, high + 1):
        shift = 12*code - offset
        expected |= 3741 << shift if shift >= 0 else 3741 >> -shift
        assert CLASS[code] == 3741
        repeat = first_repeated_bond(code)
        assert repeat is not None
        repeats[repeat] += 1
    expected &= (1 << 16384) - 1
    assert LITERALS[name] == expected
    targets.append({
        'declaration': name,
        'bits_inclusive': [offset, offset + 16383],
        'codes_inclusive': [low, high],
        'touched_codes': high - low + 1,
        'bit_offset_mod_12': offset % 12,
        'exact_sentinel_bits': True,
        'repeated_step_pairs': {f'{a},{b}': n for (a, b), n in repeats.items()},
    })

# Independently generate the paper's raw windows by adding unused unoriented bonds.
raw_codes = set()
depth_counts = Counter()


def generate(depth, code, vertex, used):
    depth_counts[depth] += 1
    if depth == 10:
        raw_codes.add(code)
        return
    for direction, (dx, dy) in enumerate(STEPS):
        end = (vertex[0] + dx, vertex[1] + dy)
        bond = tuple(sorted((vertex, end)))
        if bond not in used:
            used.add(bond)
            generate(depth + 1, 4*code + direction, end, used)
            used.remove(bond)


generate(0, 0, (0, 0), set())
assert [depth_counts[d] for d in range(1, 11)] == [
    4, 12, 36, 108, 316, 916, 2628, 7500, 21268, 60092
]
assert max(CLASS) == 3741
assert {code for code, value in enumerate(CLASS) if value < 3741} == raw_codes
assert {CLASS[code] for code in raw_codes} == set(range(3741))

print(json.dumps({
    'source': str(SOURCE),
    'targets': targets,
    'context': {
        'raw_windows': len(raw_codes),
        'invalid_codes_with_sentinel': len(CLASS) - len(raw_codes),
        'raw_coverage_matches_paper_recursion': True,
        'class_numbers_reached': len({CLASS[code] for code in raw_codes}),
        'lean_processes': 0,
    },
}, indent=2))
