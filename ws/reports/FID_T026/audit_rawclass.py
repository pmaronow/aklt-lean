"""Read-only check of the assigned literal chunks and their consumer encoding."""
from pathlib import Path
import collections
import hashlib
import json
import re

SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
source = SOURCE.read_text()
literals = {}
assemblies = {}
line_numbers = {}
for number, line in enumerate(source.splitlines(), 1):
    literal = re.fullmatch(r'private noncomputable def (\w+) : ℕ := 0x([0-9a-f]+)', line)
    assembly = re.fullmatch(r'noncomputable def (\w+) : ℕ := (.+)', line)
    if literal:
        literals[literal[1]] = int(literal[2], 16)
        line_numbers[literal[1]] = number
    elif assembly:
        assemblies[assembly[1]] = assembly[2]

class Parser:
    # The assembly uses explicitly bracketed shifts; shift binds tighter than +.
    def __init__(self, expression):
        self.tokens = re.findall(r'\w+|<<<|[()+]', expression)
        assert ''.join(self.tokens) == re.sub(r'\s+', '', expression)
        self.pos = 0

    def atom(self):
        token = self.tokens[self.pos]
        self.pos += 1
        if token == '(':
            result = self.add()
            assert self.tokens[self.pos] == ')'
            self.pos += 1
            return result
        if token.isdecimal():
            return int(token)
        assert token in literals
        return token

    def shift(self):
        result = self.atom()
        while self.pos < len(self.tokens) and self.tokens[self.pos] == '<<<':
            self.pos += 1
            amount = self.atom()
            assert isinstance(amount, int)
            result = ('shift', result, amount)
        return result

    def add(self):
        result = self.shift()
        while self.pos < len(self.tokens) and self.tokens[self.pos] == '+':
            self.pos += 1
            result = ('add', result, self.shift())
        return result

    def parse(self):
        result = self.add()
        assert self.pos == len(self.tokens)
        return result

def terms(node, offset=0):
    if isinstance(node, str):
        return [(node, offset)]
    operator, left, right = node
    if operator == 'shift':
        return terms(left, offset + right)
    assert operator == 'add'
    return terms(left, offset) + terms(right, offset)

packed = {}
placements = {}
for table, expression in assemblies.items():
    leaves = terms(Parser(expression).parse())
    assert len({name for name, offset in leaves}) == len(leaves)
    placements[table] = dict(leaves)
    # Check the numerical lengths against actual neighbor offsets: no carries.
    by_offset = sorted((offset, name) for name, offset in leaves)
    assert by_offset[0][0] == 0
    for (offset, name), (next_offset, _) in zip(by_offset, by_offset[1:]):
        assert literals[name].bit_length() <= next_offset - offset
    packed[table] = sum(literals[name] << offset for name, offset in leaves)
    print(f'{table}: parsed every literal and assembly; {len(leaves)} chunks; no overlap; bit_length={packed[table].bit_length()}')

raw_bytes = packed['rawClass'].to_bytes((12 * 4**10 + 7) // 8, 'little')
def raw_class(code):
    bit = 12 * code
    byte = bit // 8
    return (int.from_bytes(raw_bytes[byte:byte+3], 'little') >> (bit % 8)) & 4095

def word(code):
    return tuple((code >> (2 * (9 - i))) & 3 for i in range(10))

STEPS = ((1, 0), (0, 1), (-1, 0), (0, -1))
def is_raw(code):
    x, y = 0, 0
    bonds = set()
    for direction in word(code):
        dx, dy = STEPS[direction]
        endpoint = (x + dx, y + dy)
        bond = tuple(sorted(((x, y), endpoint)))
        if bond in bonds:
            return False
        bonds.add(bond)
        x, y = endpoint
    return True

results = []
for n in range(95, 100):
    name = f'rawClass_{n}'
    low = placements['rawClass'][name]
    width = 16384
    value = literals[name]
    first, last = low // 12, (low + width - 1) // 12
    codes = range(first, last + 1)
    # Each target is exactly the correct global phase of the 12-bit sentinel.
    expected = sum(3741 << (12 * j) for j in range((width + 23) // 12 + 1))
    phase = low % 12
    expected = (expected >> phase) & ((1 << width) - 1)
    assert value == expected
    values = collections.Counter(raw_class(code) for code in codes)
    raw = [code for code in codes if is_raw(code)]
    assert values == {3741: last - first + 1}
    assert not raw
    # Every affected code has an immediate N,S or W,E reversal in positions 2,3.
    assert all(word(code)[1:3] in ((1, 3), (2, 0)) for code in codes)
    result = dict(declaration=name, line=line_numbers[name],
                  bit_low=low, bit_high=low+width-1, bit_width=width,
                  phase=phase, first_code=first, last_code=last,
                  intersecting_lanes=last-first+1,
                  full_lanes=(low+width)//12-(low+11)//12,
                  raw_windows=len(raw), lane_values=dict(values),
                  first_word=''.join('ENWS'[d] for d in word(first)),
                  last_word=''.join('ENWS'[d] for d in word(last)),
                  sha256=hashlib.sha256(value.to_bytes(width//8, 'big')).hexdigest())
    results.append(result)
    print(json.dumps(result, sort_keys=True))

# Independent enumeration, using only the paper's unused-unoriented-bond rule.
raw_codes = set()
def generate(depth, code, x, y, bonds):
    if depth == 10:
        raw_codes.add(code)
        return
    for direction, (dx, dy) in enumerate(STEPS):
        endpoint = (x+dx, y+dy)
        bond = tuple(sorted(((x, y), endpoint)))
        if bond not in bonds:
            generate(depth+1, 4*code+direction, *endpoint, bonds | {bond})
generate(0, 0, 0, 0, set())
assert len(raw_codes) == 60092
coverage_errors = [code for code in range(4**10)
                   if raw_class(code) > 3741 or ((raw_class(code) < 3741) != (code in raw_codes))]
assert not coverage_errors
print(f'Full-table contextual check: {len(raw_codes)} raw windows; coverage/range errors={len(coverage_errors)}')
Path('audit_results.json').write_text(json.dumps(results, indent=2) + '\n')
