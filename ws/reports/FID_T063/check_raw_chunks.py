"""Read-only arithmetic check of the five assigned packed Nat literals."""
import ast
import re
from pathlib import Path

SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
source = SOURCE.read_text()
chunks = {
    match[1]: int(match[2], 16)
    for match in re.finditer(
        r'^private noncomputable def (rawClass_\d+) : ℕ := (0x[0-9a-f]+)$',
        source, re.MULTILINE
    )
}
expression = re.search(
    r'^noncomputable def rawClass : ℕ := (.*)$', source, re.MULTILINE
)[1]
tree = ast.parse(expression.replace('<<<', '<<'), mode='eval').body


def flatten(node, offset=0):
    if isinstance(node, ast.Name):
        return [(node.id, offset)]
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add):
        return flatten(node.left, offset) + flatten(node.right, offset)
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.LShift):
        assert isinstance(node.right, ast.Constant)
        return flatten(node.left, offset + node.right.value)
    raise ValueError(ast.dump(node))


terms = flatten(tree)
assert [name for name, _ in terms] == [f'rawClass_{i}' for i in range(768)]
ordered = sorted(terms, key=lambda term: term[1])
assert ordered[0][1] == 0
for (name, offset), (_, next_offset) in zip(ordered, ordered[1:]):
    assert chunks[name] < 1 << (next_offset - offset), 'overlap/carry'
packed = sum(chunks[name] << offset for name, offset in terms)
packed_bytes = packed.to_bytes(12 * 4**10 // 8, 'little')


def lane(code):
    byte, bit = divmod(12 * code, 8)
    return ((packed_bytes[byte] | (packed_bytes[byte + 1] << 8)) >> bit) & 4095


for number in range(280, 285):
    name = f'rawClass_{number}'
    offset = dict(terms)[name]
    first, low_bit = divmod(offset, 12)
    last = (offset + 16383) // 12
    count = last - first + 1
    repeated_sentinel = 3741 * (((1 << (12 * count)) - 1) // 4095)
    expected = (repeated_sentinel >> low_bit) & ((1 << 16384) - 1)
    assert chunks[name] == expected, 'literal differs from sentinel bits'
    for code in range(first, last + 1):
        word = [(code // 4**(9 - i)) % 4 for i in range(10)]
        assert word[:3] == [2, 2, 0]
        # W,W,E gives equal unoriented bonds at indices 1 and 2.
        x, y = 0, 0
        bonds = []
        for direction in word:
            dx, dy = [(1, 0), (0, 1), (-1, 0), (0, -1)][direction]
            new = (x + dx, y + dy)
            bonds.append(frozenset(((x, y), new)))
            x, y = new
        assert bonds[1] == bonds[2]
        assert lane(code) == 3741, 'assembled boundary lane differs'
    print(f'{name}: PASS; offset={offset}; bits={low_bit}..'
          f'{(offset + 16383) % 12}; codes={first}..{last}; '
          f'{count} touched lanes; all invalid; all markers=3741')
print('PASS: all 81,920 assigned bits and all touched boundary lanes checked.')
