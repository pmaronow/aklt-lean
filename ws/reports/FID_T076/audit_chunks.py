"""Read-only arithmetic audit of the five assigned Automaton10Data chunks."""

from pathlib import Path
import json
import re


SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
text = SOURCE.read_text()
literal_matches = list(re.finditer(
    r'^private noncomputable def (\w+) : ℕ := 0x([0-9a-f]+)$', text, re.M
))
literals = {m[1]: int(m[2], 16) for m in literal_matches}
hex_digits = {m[1]: m[2] for m in literal_matches}
source_lines = {m[1]: text.count('\n', 0, m.start()) + 1 for m in literal_matches}


class Parser:
    # Shift has higher precedence than addition. The source also parenthesizes
    # every shift in these table assembly expressions.
    def __init__(self, expression):
        self.tokens = re.findall(r'<<<|\w+|[()+]', expression)
        assert ''.join(self.tokens) == re.sub(r'\s+', '', expression)
        self.pos = 0

    def atom(self):
        token = self.tokens[self.pos]
        self.pos += 1
        if token == '(':
            node = self.add()
            assert self.tokens[self.pos] == ')'
            self.pos += 1
            return node
        if token.isdecimal():
            return ('number', int(token))
        assert token in literals
        return ('literal', token)

    def shift(self):
        node = self.atom()
        while self.pos < len(self.tokens) and self.tokens[self.pos] == '<<<':
            self.pos += 1
            amount = self.atom()
            assert amount[0] == 'number'
            node = ('shift', node, amount[1])
        return node

    def add(self):
        node = self.shift()
        while self.pos < len(self.tokens) and self.tokens[self.pos] == '+':
            self.pos += 1
            node = ('add', node, self.shift())
        return node

    def parse(self):
        node = self.add()
        assert self.pos == len(self.tokens)
        return node


def evaluate(node):
    kind = node[0]
    if kind == 'literal':
        return literals[node[1]]
    if kind == 'number':
        return node[1]
    if kind == 'shift':
        return evaluate(node[1]) << node[2]
    assert kind == 'add'
    return evaluate(node[1]) + evaluate(node[2])


def positions(node, offset=0):
    if node[0] == 'literal':
        return [(node[1], offset)]
    if node[0] == 'shift':
        return positions(node[1], offset + node[2])
    assert node[0] == 'add'
    return positions(node[1], offset) + positions(node[2], offset)


tables = {}
offsets = {}
layout = {}
total_bits = {'rawClass': 12 * 4**10, 'representatives': 20 * 3741,
              'destinations': 12 * 3741 * 4, 'edgeKinds': 2 * 3741 * 4}
for family, expected_bits in total_bits.items():
    expression = re.search(r'^noncomputable def ' + family + r' : ℕ := (.+)$', text, re.M)[1]
    node = Parser(expression).parse()
    table = evaluate(node)
    leaves = sorted(positions(node), key=lambda item: item[1])
    assert leaves[0][1] == 0
    assert len({name for name, _ in leaves}) == len(leaves)
    assert {name for name, _ in leaves} == {name for name in literals if name.startswith(family + '_')}
    for index, (name, offset) in enumerate(leaves):
        stop = leaves[index + 1][1] if index + 1 < len(leaves) else expected_bits
        assert offset < stop
        assert literals[name] < 1 << (stop - offset)
        assert (table >> offset) & ((1 << (stop - offset)) - 1) == literals[name]
        offsets[name] = (offset, stop)
    assert table.bit_length() <= expected_bits
    tables[family] = table
    layout[family] = {'chunks': len(leaves), 'reserved_bits': expected_bits,
                      'actual_bit_length': table.bit_length()}


def word(code):
    return [(code // 4**(9-i)) % 4 for i in range(10)]


steps = [(1, 0), (0, 1), (-1, 0), (0, -1)]


def raw_window(directions):
    current = (0, 0)
    bonds = set()
    for d in directions:
        dx, dy = steps[d]
        following = (current[0] + dx, current[1] + dy)
        bond = frozenset((current, following))
        if bond in bonds:
            return False
        bonds.add(bond)
        current = following
    return True


details = []
all_codes = set()
for number in range(345, 350):
    name = f'rawClass_{number}'
    lo, hi = offsets[name]
    assert hi - lo == 16384
    # Expected slice of the global infinite repetition of the 12-bit sentinel.
    repeated = sum(3741 << (12*i) for i in range((hi-lo+lo % 12+11)//12))
    expected = (repeated >> (lo % 12)) & ((1 << (hi-lo)) - 1)
    assert literals[name] == expected
    codes = range(lo // 12, (hi-1) // 12 + 1)
    assert all(0 <= code < 4**10 for code in codes)
    assert all(word(code)[:2] == [2, 0] for code in codes)
    assert all(not raw_window(word(code)) for code in codes)
    assert all((tables['rawClass'] >> (12*code)) & 4095 == 3741 for code in codes)
    all_codes.update(codes)
    details.append({
        'declaration': name,
        'source_line': source_lines[name],
        'hex_digits': len(hex_digits[name]),
        'hex_period': hex_digits[name][:3],
        'bits_half_open': [lo, hi],
        'codes_inclusive': [codes.start, codes.stop-1],
        'affected_entries': len(codes),
        'offset_mod_12': lo % 12,
        'first_word': ''.join('ENWS'[d] for d in word(codes.start)),
        'last_word': ''.join('ENWS'[d] for d in word(codes.stop-1)),
        'every_touched_entry': 3741,
        'every_touched_word_has_W_E_prefix_and_repeated_bond': True,
    })

assert len(literal_matches) == sum(item['chunks'] for item in layout.values())
print(json.dumps({'source': str(SOURCE), 'source_bytes': len(text.encode()),
                  'layout': layout, 'assigned': details,
                  'distinct_touched_entries': len(all_codes)}, indent=2))
