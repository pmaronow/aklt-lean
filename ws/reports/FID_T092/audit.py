"""Read-only audit of the five assigned packed-table chunks."""

import ast
from collections import Counter
from pathlib import Path
import re

SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
source = SOURCE.read_text()
literals = {
    name: int(value, 16)
    for name, value in re.findall(
        r'^private noncomputable def (\w+) : ℕ := 0x([0-9a-fA-F]+)$',
        source, re.M,
    )
}


def expression(name):
    value = re.search(r'^noncomputable def ' + name + r' : ℕ := (.+)$', source, re.M)[1]
    return ast.parse(value.replace('<<<', '<<'), mode='eval').body


def leaves(node, offset=0):
    if isinstance(node, ast.Name):
        return [(node.id, offset)]
    assert isinstance(node, ast.BinOp)
    if isinstance(node.op, ast.Add):
        return leaves(node.left, offset) + leaves(node.right, offset)
    assert isinstance(node.op, ast.LShift)
    assert isinstance(node.right, ast.Constant) and isinstance(node.right.value, int)
    return leaves(node.left, offset + node.right.value)


def build(name):
    chunks = leaves(expression(name))
    assert len(set(n for n, _ in chunks)) == len(chunks)
    assert set(n for n, _ in chunks) == {n for n in literals if n.startswith(name + '_')}
    ordered = sorted(chunks, key=lambda item: item[1])
    for (lo_name, lo_offset), (_, hi_offset) in zip(ordered, ordered[1:]):
        assert lo_offset + literals[lo_name].bit_length() <= hi_offset, 'overlapping chunks'
    packed = sum(literals[n] << off for n, off in chunks)
    print(name, 'chunks:', len(chunks), 'packed bit length:', packed.bit_length(),
          'disjoint supports: yes; each literal used exactly once: yes')
    return packed, dict(chunks)


packed, offsets = build('rawClass')
table = packed.to_bytes((12 * 4**10) // 8, byteorder='little')


def raw_class(code):
    bit = code * 12
    byte, rem = divmod(bit, 8)
    return (int.from_bytes(table[byte:byte + 3], 'little') >> rem) & 4095


def digits(code):
    return tuple((code >> (2 * (9-i))) & 3 for i in range(10))


step = ((1, 0), (0, 1), (-1, 0), (0, -1))


def raw_window(word):
    vertex = (0, 0)
    bonds = set()
    for direction in word:
        dx, dy = step[direction]
        next_vertex = (vertex[0] + dx, vertex[1] + dy)
        bond = frozenset((vertex, next_vertex))
        if bond in bonds:
            return False
        bonds.add(bond)
        vertex = next_vertex
    return True


affected = set()
for index in range(425, 430):
    name = f'rawClass_{index}'
    offset = offsets[name]
    value = literals[name]
    assert value < 2**16384
    assert packed >> offset & (2**16384 - 1) == value
    first, last = offset // 12, (offset + 16383) // 12
    codes = range(first, last + 1)
    affected.update(codes)
    classes = Counter(raw_class(c) for c in codes)
    prefixes = Counter(digits(c)[:2] for c in codes)
    validity = Counter(raw_window(digits(c)) for c in codes)
    assert classes == {3741: len(codes)}
    assert prefixes == {(1, 3): len(codes)}
    assert validity == {False: len(codes)}
    # Compare all bits of this chunk to the global 3741 sentinel pattern,
    # including the partial 12-bit entries at its boundaries.
    pattern = sum(3741 << (12*c - 12*first) for c in codes)
    expected = (pattern >> (offset % 12)) & (2**16384 - 1)
    assert expected == value
    print(name, 'offset:', offset, 'bit interval:', (offset, offset + 16383),
          'offset mod 12:', offset % 12, 'code interval:', (first, last),
          'hex codes:', (hex(first), hex(last)), 'entries:', len(codes),
          'class values:', dict(classes), 'first two directions:', dict(prefixes),
          'RawWindow:', dict(validity), 'all 16384 bits match sentinel: yes')

print('Unique affected codes:', len(affected), 'range:', (min(affected), max(affected)))

# Independently reconstruct the raw domain from the paper's trail recursion.
raw_codes = set()
counts = Counter()


def generate(depth, vertex, bonds, code):
    counts[depth] += 1
    if depth == 10:
        raw_codes.add(code)
        return
    for direction, (dx, dy) in enumerate(step):
        nxt = (vertex[0] + dx, vertex[1] + dy)
        bond = frozenset((vertex, nxt))
        if bond not in bonds:
            bonds.add(bond)
            generate(depth + 1, nxt, bonds, code * 4 + direction)
            bonds.remove(bond)


generate(0, (0, 0), set(), 0)
print('Independent trail counts:', [counts[j] for j in range(1, 11)])
assert [counts[j] for j in range(1, 11)] == [4,12,36,108,316,916,2628,7500,21268,60092]
assert not affected.intersection(raw_codes)
print('Affected codes in reconstructed raw domain:', len(affected.intersection(raw_codes)))
print('Assigned declaration audit: PASS')
