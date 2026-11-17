"""Read-only arithmetic audit of the five assigned packed-data declarations."""

from collections import Counter
from pathlib import Path
import re

SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
text = SOURCE.read_text()
literals = {}
line_numbers = {}
for line_no, line in enumerate(text.splitlines(), 1):
    match = re.fullmatch(r'private noncomputable def (\w+) : ℕ := 0x([0-9a-f]+)', line)
    if match:
        name, digits = match.groups()
        literals[name] = (int(digits, 16), len(digits) * 4)
        line_numbers[name] = line_no


def parse(expression):
    tokens = re.findall(r'<<<|\w+|[()+]', expression)
    assert ''.join(tokens) == re.sub(r'\s', '', expression)
    pos = 0

    def atom():
        nonlocal pos
        token = tokens[pos]
        pos += 1
        if token == '(':
            value = expr(0)
            assert tokens[pos] == ')'
            pos += 1
            return value
        if token.isdecimal():
            return int(token)
        assert token in literals
        return token

    def expr(min_precedence):
        nonlocal pos
        left = atom()
        precedence = {'<<<': 1, '+': 2}
        while pos < len(tokens) and tokens[pos] in precedence:
            op = tokens[pos]
            if precedence[op] < min_precedence:
                break
            pos += 1
            right = expr(precedence[op] + 1)
            left = (op, left, right)
        return left

    result = expr(0)
    assert pos == len(tokens)
    return result


def flattened(node, offset=0):
    if isinstance(node, str):
        return [(node, offset)]
    op, left, right = node
    if op == '<<<':
        assert isinstance(right, int)
        return flattened(left, offset + right)
    assert op == '+'
    return flattened(left, offset) + flattened(right, offset)


def assemble(name):
    expression = re.search(r'^noncomputable def ' + name + r' : ℕ := (.+)$', text, re.M)[1]
    leaves = flattened(parse(expression))
    by_offset = sorted(leaves, key=lambda item: item[1])
    end = 0
    for literal, offset in by_offset:
        assert offset == end, (literal, offset, end)
        end += literals[literal][1]
    value = sum(literals[literal][0] << offset for literal, offset in leaves)
    return value, dict(leaves), end


tables = {name: assemble(name) for name in ('rawClass', 'representatives', 'destinations', 'edgeKinds')}
packed, offsets, total_width = tables['rawClass']
print('All literal definitions parsed:', len(literals))
for name, (value, leaves, width) in tables.items():
    print(name, 'leaves', len(leaves), 'contiguous stored bits', width, 'value bits', value.bit_length())
assert len(offsets) == 768
assert set(offsets) == {f'rawClass_{i}' for i in range(768)}

# Extract using little-endian bytes; equivalent to (packed // 2**(12*c)) % 2**12.
raw_bytes = packed.to_bytes((total_width + 7) // 8, 'little')


def lane(code):
    byte, bit = divmod(12 * code, 8)
    return (int.from_bytes(raw_bytes[byte:byte+3], 'little') >> bit) & 4095


for i in range(360, 365):
    name = f'rawClass_{i}'
    value, width = literals[name]
    offset = offsets[name]
    first, last = offset // 12, (offset + width - 1) // 12
    # Compare every bit of this literal with the corresponding slice of a
    # repetition of the 12-bit sentinel, including partial boundary lanes.
    phase = offset % 12
    repetitions = (phase + width + 11) // 12
    sentinel_run = 3741 * ((1 << (12 * repetitions)) - 1) // 4095
    expected = (sentinel_run >> phase) & ((1 << width) - 1)
    assert value == expected, name
    observed = Counter(lane(code) for code in range(first, last + 1))
    assert observed == {3741: last - first + 1}, (name, observed)
    # The leading two digits in the paper's most-significant-first base-four
    # encoding are W,E (2,0), independent of all eight remaining steps.
    assert all((code // 4**9, (code // 4**8) % 4) == (2, 0)
               for code in range(first, last + 1))
    # The first bond joins (0,0) to (-1,0); the second joins the same two
    # vertices, hence the bond-index function is not injective.
    steps = ((1, 0), (0, 1), (-1, 0), (0, -1))
    for code in range(first, last + 1):
        d0, d1 = code // 4**9, (code // 4**8) % 4
        z0 = (0, 0)
        z1 = steps[d0]
        z2 = (z1[0] + steps[d1][0], z1[1] + steps[d1][1])
        assert frozenset((z0, z1)) == frozenset((z1, z2))
    print(name, 'line', line_numbers[name], 'bits', f'[{offset},{offset+width})',
          'phase', phase, 'codes', f'[{first},{last}]',
          'lanes', last - first + 1, 'values', dict(observed),
          'prefix WE; all repeat the first unoriented bond')

print('All five declarations agree bit-for-bit with the required invalid-word encoding.')
