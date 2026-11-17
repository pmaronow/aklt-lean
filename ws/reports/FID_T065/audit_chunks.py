"""Read-only reconstruction of the assigned Lean literal chunks.

Uses only the supplied Lean definitions and the paper's lattice conventions.
No Lean process, archive, or external data is needed.
"""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs')
source = (ROOT / 'Automaton10Data.lean').read_text()
literals = {
    name: int(digits, 16)
    for name, digits in re.findall(
        r'private noncomputable def (\w+) : ℕ := 0x([0-9a-f]+)', source
    )
}


def parse_expression(expression):
    tokens = re.findall(r'\w+|<<<|[()+]', expression)
    pos = 0

    def parse(min_prec=0):
        nonlocal pos
        token = tokens[pos]
        pos += 1
        if token == '(':
            tree = parse()
            assert tokens[pos] == ')'
            pos += 1
        else:
            tree = token
        precedence = {'+': 10, '<<<': 20}
        while pos < len(tokens) and precedence.get(tokens[pos], -1) >= min_prec:
            op = tokens[pos]
            pos += 1
            rhs = parse(precedence[op] + 1)
            tree = (op, tree, rhs)
        return tree

    tree = parse()
    assert pos == len(tokens)
    return tree


def evaluate(tree):
    if isinstance(tree, str):
        return int(tree) if tree.isdigit() else literals[tree]
    op, left, right = tree
    a, b = evaluate(left), evaluate(right)
    return a + b if op == '+' else a << b


def offsets(tree, offset=0):
    if isinstance(tree, str):
        return [(tree, offset)]
    op, left, right = tree
    if op == '<<<':
        return offsets(left, offset + evaluate(right))
    return offsets(left, offset) + offsets(right, offset)


packed = {}
places = {}
for table in ('rawClass', 'representatives', 'destinations', 'edgeKinds'):
    expression = re.search(
        rf'^noncomputable def {table} : ℕ := (.+)$', source, re.M
    ).group(1)
    tree = parse_expression(expression)
    packed[table] = evaluate(tree)
    places[table] = dict(offsets(tree))

# Confirm the huge assembly expression concatenates every chunk once,
# with no overlaps, unfilled internal gaps, or carries from addition.
chunk_order = sorted(places['rawClass'], key=lambda n: places['rawClass'][n])
assert len(chunk_order) == 768
assert places['rawClass'][chunk_order[0]] == 0
for low, high in zip(chunk_order, chunk_order[1:]):
    width = places['rawClass'][high] - places['rawClass'][low]
    assert width == (16380 if low == 'rawClass_767' else 16384)
    assert literals[low] < 1 << width

widths = {'rawClass': 12, 'representatives': 20, 'destinations': 12, 'edgeKinds': 2}
buffers = {
    table: number.to_bytes((number.bit_length() + 7) // 8, 'little')
    for table, number in packed.items()
}


def lane(table, index):
    width = widths[table]
    first_bit = width * index
    first_byte, bit_offset = divmod(first_bit, 8)
    count = (width + bit_offset + 7) // 8
    return (int.from_bytes(buffers[table][first_byte:first_byte + count], 'little')
            >> bit_offset) & ((1 << width) - 1)


def word(code):
    return tuple((code >> (2 * (9 - i))) & 3 for i in range(10))


STEPS = ((1, 0), (0, 1), (-1, 0), (0, -1))


def geometry(directions):
    x = y = 0
    bonds = set()
    vertices = [(x, y)]
    for d in directions:
        dx, dy = STEPS[d]
        end = x + dx, y + dy
        bond = frozenset(((x, y), end))
        if bond in bonds:
            return None
        bonds.add(bond)
        x, y = end
        vertices.append(end)
    return vertices, bonds


results = []
for j in range(290, 295):
    name = f'rawClass_{j}'
    digits = re.search(rf'def {name} : ℕ := 0x([0-9a-f]+)', source).group(1)
    offset = places['rawClass'][name]
    width = 4 * len(digits)
    # Every lane touched, including partially covered boundary lanes.
    first = offset // 12
    last = (offset + width - 1) // 12
    codes = range(first, last + 1)
    values = sorted({lane('rawClass', code) for code in codes})
    invalid = sum(geometry(word(code)) is None for code in codes)
    adjacent_reversal = sum(
        any((a + 2) % 4 == b for a, b in zip(word(code), word(code)[1:]))
        for code in codes
    )
    # Reconstruct every assigned bit from the sentinel value at the
    # GLOBAL lane positions; local 12-bit alignment differs by chunk.
    expected = 0
    for code in codes:
        bit_start = 12 * code - offset
        if bit_start >= 0:
            expected |= 3741 << bit_start
        else:
            expected |= 3741 >> -bit_start
    expected &= (1 << width) - 1
    row = dict(
        declaration=name,
        lean_line=source[:source.index('private noncomputable def ' + name + ' ')].count('\n') + 1,
        hex_digits=len(digits),
        hex_sha256=hashlib.sha256(digits.encode()).hexdigest(),
        global_low_bit=offset,
        global_high_bit=offset + width - 1,
        first_code=first,
        last_code=last,
        touched_lanes=last - first + 1,
        decoded_class_values=values,
        invalid_raw_words=invalid,
        words_with_adjacent_reversal=adjacent_reversal,
        literal_matches_global_sentinel_pattern=literals[name] == expected,
        first_word=word(first),
        last_word=word(last),
    )
    assert values == [3741]
    assert invalid == len(codes)
    assert literals[name] == expected
    assert all(word(code)[:3] == (2, 1, 3) for code in codes)
    results.append(row)

print(json.dumps({
    'chunks': results,
    'distinct_affected_words': len({
        code for row in results
        for code in range(row['first_code'], row['last_code'] + 1)
    }),
    'common_prefix': ['W', 'N', 'S'],
}, indent=2))
