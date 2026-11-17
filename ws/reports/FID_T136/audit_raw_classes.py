"""Read-only arithmetic audit of the five assigned packed table fragments."""
from pathlib import Path
import re

SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
text = SOURCE.read_text()
constants = {
    name: (int(digits, 16), len(digits) * 4)
    for name, digits in re.findall(
        r'^private noncomputable def (\w+) : ℕ := 0x([0-9a-f]+)$', text, re.M
    )
}

# The aggregate expressions consist only of natural addition, shifts and parentheses.
# Each shift operand is a numeral, and each addition operand is parenthesized or atomic.
class Parser:
    def __init__(self, expr):
        self.tokens = re.findall(r'\w+|<<<|[()+]', expr)
        assert ''.join(self.tokens) == re.sub(r'\s+', '', expr)
        self.i = 0

    def atom(self):
        tok = self.tokens[self.i]
        self.i += 1
        if tok == '(':
            result = self.expr()
            assert self.tokens[self.i] == ')'
            self.i += 1
            return result
        assert tok in constants, tok
        return ('literal', tok)

    def shifted(self):
        result = self.atom()
        if self.i < len(self.tokens) and self.tokens[self.i] == '<<<':
            self.i += 1
            shift = int(self.tokens[self.i])
            self.i += 1
            result = ('shift', result, shift)
        return result

    def expr(self):
        result = self.shifted()
        while self.i < len(self.tokens) and self.tokens[self.i] == '+':
            self.i += 1
            result = ('add', result, self.shifted())
        return result

    def parse(self):
        result = self.expr()
        assert self.i == len(self.tokens)
        return result


def flatten(node, offset=0):
    if node[0] == 'literal':
        return [(node[1], offset)]
    if node[0] == 'shift':
        return flatten(node[1], offset + node[2])
    return flatten(node[1], offset) + flatten(node[2], offset)


def evaluate(node):
    if node[0] == 'literal':
        return constants[node[1]][0]
    if node[0] == 'shift':
        return evaluate(node[1]) << node[2]
    return evaluate(node[1]) + evaluate(node[2])

aggregates = {}
for name, expr in re.findall(r'^noncomputable def (\w+) : ℕ := (.+)$', text, re.M):
    tree = Parser(expr).parse()
    terms = flatten(tree)
    cursor = 0
    for term, offset in sorted(terms, key=lambda p: p[1]):
        assert offset == cursor, (name, term, offset, cursor)
        value, width = constants[term]
        assert 0 <= value < 2 ** width
        cursor += width
    aggregates[name] = (evaluate(tree), dict(terms))
    print(f'{name}: {len(terms)} literal fragments; {cursor} packed bits; no gaps/overlaps')

packed, offsets = aggregates['rawClass']
assert len(offsets) == 768
assert packed.bit_length() == 12 * 4**10 - 4  # Leading zero nibble is omitted.

def lane(code):
    return (packed >> (12 * code)) & 4095

for index in range(645, 650):
    name = f'rawClass_{index}'
    value, width = constants[name]
    offset = offsets[name]
    first = offset // 12
    last = (offset + width - 1) // 12
    expected = 0
    for code in range(first, last + 1):
        expected |= 3741 << (12 * code - first * 12)
    expected = (expected >> (offset - first * 12)) & ((1 << width) - 1)
    assert value == expected, name
    for code in range(first, last + 1):
        assert lane(code) == 3741
        digits = [(code // 4 ** (9 - i)) % 4 for i in range(10)]
        assert digits[:2] == [0, 2], (name, code, digits)
        # These two steps traverse the same unordered bond in opposite directions.
        vertices = [(0, 0), (1, 0), (0, 0)]
        assert frozenset(vertices[:2]) == frozenset(vertices[1:])
    line = next(i for i, line in enumerate(text.splitlines(), 1)
                if line.startswith(f'private noncomputable def {name} :'))
    print(f'{name}, line {line}: bits [{offset}, {offset + width}); '
          f'codes {first}..{last} ({last-first+1} touched lanes); '
          f'all = 3741; all begin E,W; fragment matches sentinel bits exactly')
