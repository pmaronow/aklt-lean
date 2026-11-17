"""Independent finite audit of the Lean literals against the paper's contract.
Reads only the authorized Lean source. No Lean process or input mutation.
"""
from pathlib import Path
from collections import Counter
import json
import re

SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
source = SOURCE.read_text()
literals = {}
literal_widths = {}
expressions = {}
line_numbers = {}
for number, line in enumerate(source.splitlines(), 1):
    match = re.fullmatch(r'(?:private )?noncomputable def (\w+) : ℕ := (.+)', line)
    if match:
        name, body = match.groups()
        line_numbers[name] = number
        if re.fullmatch(r'0x[0-9a-f]+', body):
            literals[name] = int(body, 16)
            literal_widths[name] = 4*(len(body)-2)
        else:
            expressions[name] = body

# Parse every table assembly expression, preserving the offset of every leaf.
class Parser:
    def __init__(self, expression):
        self.tokens = re.findall(r'<<<|[()+]|\w+', expression)
        assert ''.join(self.tokens) == re.sub(r'\s', '', expression)
        self.index = 0

    def primary(self):
        token = self.tokens[self.index]
        self.index += 1
        if token == '(':
            result = self.expression()
            assert self.tokens[self.index] == ')'
            self.index += 1
            return result
        assert token in literals, token
        return literals[token], {token: 0}

    def expression(self):
        value, positions = self.primary()
        while self.index < len(self.tokens) and self.tokens[self.index] != ')':
            operator = self.tokens[self.index]
            self.index += 1
            if operator == '<<<':
                amount = int(self.tokens[self.index])
                self.index += 1
                value <<= amount
                positions = {name: offset + amount for name, offset in positions.items()}
            else:
                assert operator == '+'
                other, other_positions = self.primary()
                assert not positions.keys() & other_positions.keys()
                value += other
                positions.update(other_positions)
        return value, positions

    def parse(self):
        result = self.expression()
        assert self.index == len(self.tokens)
        return result

packed = {}
positions = {}
for name, expression in expressions.items():
    packed[name], positions[name] = Parser(expression).parse()
    for leaf, offset in positions[name].items():
        assert ((packed[name] >> offset) & ((1 << literal_widths[leaf])-1)) == literals[leaf], (name, leaf, offset)
    ordered = sorted(positions[name].items(), key=lambda item: item[1])
    assert ordered[0][1] == 0
    assert all(a[1] + literal_widths[a[0]] == b[1]
               for a, b in zip(ordered, ordered[1:])), (name, 'overlap')

assert len(literals) == 768 + 5 + 11 + 2
assert set(packed) == {'rawClass', 'representatives', 'destinations', 'edgeKinds'}
assert all(positions['rawClass'][f'rawClass_{j}'] == (767-j)*16384-4 for j in range(767))
assert positions['rawClass']['rawClass_767'] == 0
assert packed['rawClass'].bit_length() <= 12*4**10

# Efficient exact decoding: two 12-bit lanes per three little-endian bytes.
raw_bytes = packed['rawClass'].to_bytes(12*4**10//8, 'little')
raw_class = []
for start in range(0, len(raw_bytes), 3):
    pair = int.from_bytes(raw_bytes[start:start+3], 'little')
    raw_class.extend((pair & 4095, pair >> 12))
assert len(raw_class) == 4**10

def lanes(table, width, count):
    value = packed[table]
    mask = (1 << width)-1
    output = []
    for _ in range(count):
        output.append(value & mask)
        value >>= width
    assert value == 0
    return output

representatives = lanes('representatives', 20, 3741)
destinations = lanes('destinations', 12, 3741*4)
kinds = lanes('edgeKinds', 2, 3741*4)
assert all(x <= 3741 for x in raw_class)
assert all(x < 4**10 for x in representatives)
assert all(0 <= x <= 3741 for x in destinations)
assert all((dest == 0) == (kind == 3) for dest, kind in zip(destinations, kinds))

# Independent paper recursion: actual coordinates, unordered bonds, E,N,W,S.
steps = ((1,0), (0,1), (-1,0), (0,-1))
counts = [0]*11
raw_states = {}

def extend(word, vertices, bonds, code):
    depth = len(word)
    counts[depth] += 1
    if depth == 10:
        raw_states[code] = (word, vertices, frozenset(bonds))
        return
    x, y = vertices[-1]
    for direction, (dx, dy) in enumerate(steps):
        endpoint = (x+dx, y+dy)
        bond = frozenset((vertices[-1], endpoint))
        if bond not in bonds:
            extend(word+(direction,), vertices+(endpoint,), bonds | {bond}, 4*code+direction)

extend((), ((0,0),), set(), 0)
assert counts == [1,4,12,36,108,316,916,2628,7500,21268,60092], counts
assert list(raw_states) == sorted(raw_states)
assert {code for code, a in enumerate(raw_class) if a < 3741} == raw_states.keys()
assert all(code in raw_states and raw_class[code] == a for a, code in enumerate(representatives))

# Regenerate all four labelled transitions of every raw word.
# Paper kind is relevant for admitted edges; masked invalid edges have code 3.
def regenerate(state):
    word, vertices, bonds = state
    x, y = vertices[-1]
    revisit = vertices[-1] in vertices[:-1]
    result = []
    for direction, (dx, dy) in enumerate(steps):
        new_bond = frozenset((vertices[-1], (x+dx,y+dy)))
        admitted = direction != (word[-1]+2)%4 and new_bond not in bonds
        kind = 2 if revisit else 0 if direction == word[-1] else 1
        result.append((admitted, kind))
    return result

rep_rows = [regenerate(raw_states[code]) for code in representatives]
checks = Counter()
for code, state in raw_states.items():
    word, vertices, bonds = state
    a = raw_class[code]
    row = regenerate(state)
    for d, (admitted, kind) in enumerate(row):
        index = a*4+d
        assert admitted == (destinations[index] != 0), (code, a, d, 'admissibility')
        checks['admissibility'] += 1
        # The paper's quotient lemma also asks identical kinds on each absolute
        # direction, including inadmissible directions; compare the raw reps.
        assert kind == rep_rows[a][d][1], (code,a,d,'raw kind vs representative')
        checks['raw_kind_vs_representative'] += 1
        if admitted:
            successor_code = (code % 4**9)*4+d
            assert successor_code in raw_states
            assert destinations[index]-1 == raw_class[successor_code], (code,a,d,'successor')
            assert kinds[index] == kind, (code,a,d,'stored kind')
            checks['admitted_successor_and_kind'] += 1
            if kind != 2:
                assert word[-1] == representatives[a] % 4, (code,a,d,'arrival')
                checks['nonrevisit_arrival'] += 1

edge_counts = Counter(kind for dest,kind in zip(destinations,kinds) if dest)
assert edge_counts == {0:2516,1:5032,2:1872}, edge_counts

summary = {
    'literal_count': len(literals),
    'assembly_offsets_and_nonoverlap': 'PASS',
    'all_raw_codes': len(raw_class),
    'counts_by_length': counts,
    'raw_windows': len(raw_states),
    'invalid_sentinels': raw_class.count(3741),
    'representatives_checked': len(representatives),
    'row_checks': dict(checks),
    'quotient_edge_counts': dict(edge_counts),
    'targets': {},
}
for j in range(300,305):
    name = f'rawClass_{j}'
    low = positions['rawClass'][name]
    high = low+16384
    first, last = low//12, (high-1)//12
    full_first, full_last = (low+11)//12, high//12-1
    raw_codes = [code for code in range(first,last+1) if code in raw_states]
    sample = raw_codes[:3]
    summary['targets'][name] = {
        'source_line': line_numbers[name],
        'bit_interval_half_open': [low,high],
        'intersecting_code_interval_inclusive': [first,last],
        'full_lane_interval_inclusive': [full_first,full_last],
        'raw_windows_intersecting': len(raw_codes),
        'invalid_codes_intersecting': last-first+1-len(raw_codes),
        'sample_code_class_word': [[code,raw_class[code], ''.join('ENWS'[d] for d in raw_states[code][0])] for code in sample],
    }
print(json.dumps(summary,indent=2))
