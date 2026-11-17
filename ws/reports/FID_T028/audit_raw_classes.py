"""Read-only audit of the supplied packed data and the five assigned chunks."""

from collections import Counter
from pathlib import Path
import json
import re


SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
text = SOURCE.read_text()
literal_rows = re.findall(
    r'^private noncomputable def (\w+) : ℕ := 0x([0-9a-f]+)$', text, re.M
)
literals = {name: int(digits, 16) for name, digits in literal_rows}
hex_digits = dict(literal_rows)


class Parser:
    def __init__(self, expression):
        self.tokens = re.findall(r'<<<|\w+|[()+]', expression)
        assert ''.join(self.tokens) == re.sub(r'\s+', '', expression)
        self.pos = 0

    def atom(self):
        token = self.tokens[self.pos]
        self.pos += 1
        if token == '(':
            result = self.expression()
            assert self.tokens[self.pos] == ')'
            self.pos += 1
            return result
        assert token in literals, token
        return ('literal', token)

    def shifted(self):
        result = self.atom()
        while self.pos < len(self.tokens) and self.tokens[self.pos] == '<<<':
            self.pos += 1
            count = int(self.tokens[self.pos])
            self.pos += 1
            result = ('shift', result, count)
        return result

    def expression(self):
        result = self.shifted()
        while self.pos < len(self.tokens) and self.tokens[self.pos] == '+':
            self.pos += 1
            result = ('add', result, self.shifted())
        return result


def evaluate(node, offset=0, leaves=None):
    if node[0] == 'literal':
        if leaves is not None:
            leaves.append((offset, node[1], len(hex_digits[node[1]]) * 4))
        return literals[node[1]]
    if node[0] == 'shift':
        return evaluate(node[1], offset + node[2], leaves) << node[2]
    return evaluate(node[1], offset, leaves) + evaluate(node[2], offset, leaves)


tables = {}
leaf_tables = {}
for name in ('rawClass', 'representatives', 'destinations', 'edgeKinds'):
    expression = re.search(rf'^noncomputable def {name} : ℕ := (.+)$', text, re.M)[1]
    parser = Parser(expression)
    tree = parser.expression()
    assert parser.pos == len(parser.tokens)
    leaves = []
    tables[name] = evaluate(tree, leaves=leaves)
    leaf_tables[name] = leaves
    # Declared hex widths, including leading zeros, must be disjoint and gapless.
    ordered = sorted(leaves)
    assert ordered[0][0] == 0
    for (off, _, width), (next_off, _, _) in zip(ordered, ordered[1:]):
        assert off + width == next_off, (name, off, width, next_off)


packed_bytes = {
    name: value.to_bytes((value.bit_length() + 7) // 8, 'little')
    for name, value in tables.items()
}


def lane(name, width, index):
    bit = width * index
    start = bit // 8
    size = (bit % 8 + width + 7) // 8
    data = int.from_bytes(packed_bytes[name][start:start + size], 'little')
    return (data >> (bit % 8)) & ((1 << width) - 1)


steps = ((1, 0), (0, 1), (-1, 0), (0, -1))


def decode(code):
    return tuple((code >> (2 * (9 - i))) & 3 for i in range(10))


def raw_and_first_repetition(code):
    x = y = 0
    used = {}
    for i, d in enumerate(decode(code)):
        dx, dy = steps[d]
        nx, ny = x + dx, y + dy
        bond = frozenset(((x, y), (nx, ny)))
        if bond in used:
            return False, (used[bond], i)
        used[bond] = i
        x, y = nx, ny
    return True, None


summaries = []
for offset, name, width in leaf_tables['rawClass']:
    if name not in {f'rawClass_{i}' for i in range(105, 110)}:
        continue
    value = literals[name]
    # Check every nibble against a globally aligned repetition of sentinel 3741.
    for j, digit in enumerate(reversed(hex_digits[name])):
        assert int(digit, 16) == ((3741 >> ((offset + 4 * j) % 12)) & 15)
    first_code = offset // 12
    last_code = (offset + width - 1) // 12
    repetitions = Counter()
    for code in range(first_code, last_code + 1):
        assert lane('rawClass', 12, code) == 3741, (name, code)
        raw, repeated = raw_and_first_repetition(code)
        assert not raw, (name, code)
        repetitions[repeated] += 1
    summaries.append({
        'declaration': name,
        'source_line': text[:text.index(f'private noncomputable def {name} :')].count('\n') + 1,
        'bit_interval_inclusive': [offset, offset + width - 1],
        'touched_code_interval_inclusive': [first_code, last_code],
        'touched_codes': last_code - first_code + 1,
        'first_word_ENWS_digits': ''.join(map(str, decode(first_code))),
        'last_word_ENWS_digits': ''.join(map(str, decode(last_code))),
        'repeated_bond_zero_based_indices': {str(k): v for k, v in sorted(repetitions.items())},
        'all_touched_lanes_equal_3741': True,
        'all_touched_words_repeat_bond': True,
        'low_end_bit_position_mod_12': offset % 12,
    })

result = {
    'source_lines': len(text.splitlines()),
    'literal_declarations_parsed': len(literals),
    'all_four_table_expressions_parsed': True,
    'all_table_chunks_disjoint_and_gapless': True,
    'table_widths': {
        name: max(off + width for off, _, width in leaves)
        for name, leaves in leaf_tables.items()
    },
    'assigned_chunks': sorted(summaries, key=lambda row: row['source_line']),
}
print(json.dumps(result, indent=2))
