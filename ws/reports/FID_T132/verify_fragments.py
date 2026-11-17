"""Read-only exact-integer audit of the five assigned packed-table fragments."""
from pathlib import Path
import re

SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
text = SOURCE.read_text()
literals = {}
source_lines = {}
for line_number, line in enumerate(text.splitlines(), 1):
    match = re.fullmatch(r'private noncomputable def (\w+) : ℕ := 0x([0-9a-f]+)', line)
    if match:
        name, digits = match.groups()
        assert name not in literals
        literals[name] = int(digits, 16)
        source_lines[name] = line_number
assert len(literals) == 786

# Parse every aggregate expression using only its actual parentheses, +, and <<<.
# Return both its exact integer and each constituent's global bit offset.
class Parser:
    def __init__(self, expression):
        self.tokens = re.findall(r'\w+|<<<|[()+]', expression)
        assert ''.join(self.tokens) == re.sub(r'\s+', '', expression)
        self.position = 0

    def take(self):
        token = self.tokens[self.position]
        self.position += 1
        return token

    def atom(self):
        token = self.take()
        if token == '(':
            result = self.expression()
            assert self.take() == ')'
            return result
        if token.isdecimal():
            return int(token), {}
        return literals[token], {token: 0}

    def expression(self):
        result, offsets = self.atom()
        while self.position < len(self.tokens) and self.tokens[self.position] != ')':
            operator = self.take()
            other, more_offsets = self.atom()
            if operator == '<<<':
                assert not more_offsets
                result <<= other
                offsets = {name: offset + other for name, offset in offsets.items()}
            else:
                assert operator == '+'
                assert not (offsets.keys() & more_offsets.keys())
                result += other
                offsets.update(more_offsets)
        return result, offsets

aggregates = {}
offsets = {}
for name, expression in re.findall(r'^noncomputable def (\w+) : ℕ := (.+)$', text, re.M):
    parser = Parser(expression)
    value, placements = parser.expression()
    assert parser.position == len(parser.tokens)
    # The source additions are concatenations, with no carries between chunks.
    ordered = sorted(placements.items(), key=lambda item: item[1])
    assert ordered[0][1] == 0
    for (lower_name, lower_offset), (_, higher_offset) in zip(ordered, ordered[1:]):
        assert literals[lower_name] < 1 << (higher_offset - lower_offset)
    assert value == sum(literals[part] << offset for part, offset in ordered)
    aggregates[name] = value
    offsets.update(placements)
assert set(aggregates) == {'rawClass', 'representatives', 'destinations', 'edgeKinds'}
assert len(offsets) == len(literals)

# Independent high-to-low hexadecimal concatenation corroborates tree evaluation.
raw_parts = [literals[f'rawClass_{i}'] for i in range(768)]
raw_hex = ''.join(f'{part:04096x}' for part in raw_parts[:-1]) + f'{raw_parts[-1]:04095x}'
assert int(raw_hex, 16) == aggregates['rawClass']


def lane(code):
    # Take a small byte slice to avoid repeatedly shifting the entire huge table.
    bit = 12 * code
    start, intra_byte = divmod(bit, 8)
    return (int.from_bytes(raw_bytes[start:start + 3], 'little') >> intra_byte) & 4095

raw_bytes = aggregates['rawClass'].to_bytes((12 * 4**10 + 7) // 8, 'little')
periodic_sentinel = sum(3741 << (12 * i) for i in range(1368))
print('Parsed entire source: 786 literals, all 4 concatenation trees, all chunk offsets.')
all_codes = set()
for i in range(625, 630):
    name = f'rawClass_{i}'
    offset = offsets[name]
    width = 16384
    assert offset == (767 - i) * 16384 - 4
    assert literals[name] == (periodic_sentinel >> (offset % 12)) & ((1 << width) - 1)
    lower, upper = offset // 12, (offset + width - 1) // 12
    for code in range(lower, upper + 1):
        assert lane(code) == 3741  # Includes every boundary lane's neighboring bits.
        digits = [(code // 4**(9 - j)) % 4 for j in range(10)]
        assert digits[:2] == [0, 2]  # E,W retraces the very first unoriented bond.
    all_codes.update(range(lower, upper + 1))
    print(f'{name}: line={source_lines[name]}, bits=[{offset},{offset + width - 1}], '
          f'offset%12={offset%12}, intersected_codes=[{lower},{upper}], '
          f'hex_codes=[{lower:#x},{upper:#x}], lanes={upper-lower+1}; '
          'exact sentinel pattern; all decoded lanes=3741; all words start E,W')
print(f'PASS: all {len(all_codes)} distinct affected codes are nonraw words.')
