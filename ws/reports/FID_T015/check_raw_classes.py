"""Read-only audit of the supplied Lean literals against the paper's trail rules."""

import ast
from collections import Counter
from pathlib import Path
import re


SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
TEXT = SOURCE.read_text()
LITERALS = {
    name: (int(digits, 16), 4 * len(digits))
    for name, digits in re.findall(
        r'^private noncomputable def (\w+) : ℕ := 0x([0-9a-f]+)$', TEXT, re.M
    )
}


def flatten(node, offset=0):
    if isinstance(node, ast.Name):
        return [(node.id, offset)]
    assert isinstance(node, ast.BinOp)
    if isinstance(node.op, ast.LShift):
        assert isinstance(node.right, ast.Constant)
        return flatten(node.left, offset + node.right.value)
    assert isinstance(node.op, ast.Add)
    return flatten(node.left, offset) + flatten(node.right, offset)


def unpack(name, width, count):
    expression = re.search(
        r'^noncomputable def ' + name + r' : ℕ := (.*)$', TEXT, re.M
    )[1]
    tree = ast.parse(expression.replace('<<<', '<<'), mode='eval').body
    parts = flatten(tree)
    assert len({part for part, _ in parts}) == len(parts)
    previous_end = 0
    for part, offset in sorted(parts, key=lambda p: p[1]):
        literal, capacity = LITERALS[part]
        assert offset == previous_end, (part, offset, previous_end)
        assert literal < 2**capacity
        previous_end = offset + capacity
    packed = sum(LITERALS[part][0] << offset for part, offset in parts)
    assert packed < 2 ** (width * count)
    # The leading zero nibble is implicit in rawClass's first lane.
    data = packed.to_bytes((width * count + 7) // 8, 'little')
    mask = (1 << width) - 1
    lanes = []
    for index in range(count):
        bit = width * index
        byte, shift = divmod(bit, 8)
        lanes.append((int.from_bytes(data[byte:byte + 4], 'little') >> shift) & mask)
    print(f'{name}: {len(parts)} nonoverlapping chunks; {count} lanes; max={max(lanes)}')
    return lanes, dict(parts)


RAW, OFFSETS = unpack('rawClass', 12, 4**10)
REP, _ = unpack('representatives', 20, 3741)
DEST, _ = unpack('destinations', 12, 4 * 3741)
KIND, _ = unpack('edgeKinds', 2, 4 * 3741)
assert all(value <= 3741 for value in RAW)
assert all(value < 4**10 for value in REP)
assert all(value <= 3741 for value in DEST)
for destination, kind in zip(DEST, KIND):
    assert (destination == 0) == (kind == 3)
    assert destination == 0 or kind < 3

STEPS = ((1, 0), (0, 1), (-1, 0), (0, -1))
COUNTS = [0] * 11
WINDOWS = {}


def bond(a, b):
    return tuple(sorted((a, b)))


def generate(word=(), code=0, position=(0, 0), vertices=((0, 0),), bonds=frozenset()):
    depth = len(word)
    COUNTS[depth] += 1
    if depth == 10:
        WINDOWS[code] = (word, position, vertices[:-1], bonds)
        return
    for direction, (dx, dy) in enumerate(STEPS):
        nxt = (position[0] + dx, position[1] + dy)
        edge = bond(position, nxt)
        if edge not in bonds:
            generate(word + (direction,), code * 4 + direction, nxt,
                     vertices + (nxt,), bonds | {edge})


generate()
assert COUNTS[1:] == [4, 12, 36, 108, 316, 916, 2628, 7500, 21268, 60092]
assert all((value < 3741) == (code in WINDOWS) for code, value in enumerate(RAW))
assert set(RAW[code] for code in WINDOWS) == set(range(3741))
for cls, code in enumerate(REP):
    assert code in WINDOWS and RAW[code] == cls, (cls, code, RAW[code])


def row(window):
    word, position, previous_vertices, bonds = window
    revisit = position in previous_vertices
    result = []
    for direction, (dx, dy) in enumerate(STEPS):
        nxt = (position[0] + dx, position[1] + dy)
        allowed = direction != (word[-1] + 2) % 4 and bond(position, nxt) not in bonds
        kind = 2 if revisit else 0 if direction == word[-1] else 1
        result.append((allowed, kind))
    return result


REP_ROWS = [row(WINDOWS[code]) for code in REP]
EDGE_COUNTS = Counter()
for cls, code in enumerate(REP):
    for direction, (allowed, kind) in enumerate(REP_ROWS[cls]):
        index = 4 * cls + direction
        assert bool(DEST[index]) == allowed, (cls, direction, 'representative admissibility')
        if allowed:
            successor = (code % 4**9) * 4 + direction
            assert successor in WINDOWS
            assert KIND[index] == kind, (cls, direction, 'stored kind')
            assert DEST[index] - 1 == RAW[successor], (cls, direction, 'stored successor')
            EDGE_COUNTS[kind] += 1
assert EDGE_COUNTS == Counter({0: 2516, 1: 5032, 2: 1872})

for code, window in WINDOWS.items():
    cls = RAW[code]
    raw_row = row(window)
    assert raw_row == REP_ROWS[cls], (code, cls, 'admissibility/kind, all directions')
    for direction, (allowed, kind) in enumerate(raw_row):
        if allowed:
            successor = (code % 4**9) * 4 + direction
            assert successor in WINDOWS
            assert DEST[4 * cls + direction] - 1 == RAW[successor], (code, direction, 'successor')
            if kind != 2:
                assert window[0][-1] == WINDOWS[REP[cls]][0][-1], (code, cls, 'arrival')

print('Raw counts at depths 1..10:', COUNTS[1:])
print('All 1048576 codes: raw coverage/range correct; 60092 valid, 988484 sentinel lanes.')
print('All 3741 representatives: raw, assigned to own class; surjectivity verified.')
print('All 60092 raw windows x 4 directions: admissibility, kind (even forbidden directions),')
print('  admissible successor class and nonrevisit arrival comparisons passed.')
print('Regenerated labelled edge counts:', dict(sorted(EDGE_COUNTS.items())))

for index in range(40, 45):
    name = f'rawClass_{index}'
    offset = OFFSETS[name]
    value, capacity = LITERALS[name]
    first = offset // 12
    last = (offset + capacity - 1) // 12
    touched = range(first, last + 1)
    valid = [code for code in touched if code in WINDOWS]
    invalid = [code for code in touched if code not in WINDOWS]
    # Reconstruct every bit in the assigned literal from the validated lanes,
    # including the pieces of lanes shared with its adjacent chunks.
    reconstructed = sum(RAW[code] << (12 * (code - first)) for code in touched)
    reconstructed = (reconstructed >> (offset % 12)) & ((1 << capacity) - 1)
    assert reconstructed == value
    sample = [(code, RAW[code], REP[RAW[code]]) for code in valid[:3]]
    print(f'{name}: bit interval [{offset},{offset + capacity}); codes [{first},{last}];')
    print(f'  {len(touched)} affected lanes = {len(valid)} raw + {len(invalid)} invalid;')
    print(f'  distinct valid classes={len({RAW[code] for code in valid})}; sample(code,class,rep)={sample};')
    print(f'  all {capacity} bits reconstructed exactly; PASS')

print('PASS: all checks completed.')
