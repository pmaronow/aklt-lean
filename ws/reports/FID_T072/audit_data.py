"""Read-only audit of the supplied literals against the paper's trail recursion."""
from pathlib import Path
from collections import Counter
import hashlib
import json
import re

SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
source = SOURCE.read_text()
literal_hex = dict(re.findall(
    r'(?:private )?noncomputable def (\w+) : ℕ := (0x[0-9a-f]+)', source))
literals = {name: int(h, 16) for name, h in literal_hex.items()}


def parse(expression):
    """Parse the actual parenthesized Lean +/<<< expression, preserving leaves."""
    tokens = re.findall(r'<<<|\w+|[()+]', expression)
    assert ''.join(tokens) == re.sub(r'\s+', '', expression)
    pos = 0

    def expr(min_prec=0):
        nonlocal pos
        token = tokens[pos]
        pos += 1
        if token == '(':
            node = expr()
            assert tokens[pos] == ')'
            pos += 1
        else:
            node = int(token) if token.isdigit() else token
        while pos < len(tokens) and tokens[pos] in ('+', '<<<'):
            op = tokens[pos]
            prec = {'+': 65, '<<<': 75}[op]
            if prec < min_prec:
                break
            pos += 1
            node = (op, node, expr(prec + 1))
        return node

    node = expr()
    assert pos == len(tokens)
    return node


def evaluate(node):
    if isinstance(node, int):
        return node
    if isinstance(node, str):
        return literals[node]
    op, left, right = node
    a, b = evaluate(left), evaluate(right)
    return a + b if op == '+' else a << b


def placements(node, offset=0):
    if isinstance(node, str):
        return [(node, offset)]
    op, left, right = node
    if op == '+':
        return placements(left, offset) + placements(right, offset)
    return placements(left, offset + evaluate(right))


tables = {}
positions = {}
for name in ('rawClass', 'representatives', 'destinations', 'edgeKinds'):
    expression = re.search(rf'^noncomputable def {name} : ℕ := (.+)$', source, re.M)[1]
    tree = parse(expression)
    value = evaluate(tree)
    layout = placements(tree)
    # Verify every addition really concatenates disjoint, correctly ordered chunks.
    offset = 0
    for chunk, actual_offset in reversed(layout):
        assert actual_offset == offset, (chunk, actual_offset, offset)
        width = 4 * (len(literal_hex[chunk]) - 2)
        assert literals[chunk] < 1 << width
        offset += width
    assert len(set(n for n, _ in layout)) == len(layout)
    assert value == int(''.join(literal_hex[n][2:] for n, _ in layout), 16)
    tables[name] = value.to_bytes((value.bit_length() + 7) // 8, 'little') + b'\0' * 8
    positions[name] = dict(layout)


def lane(table, width, index):
    bit = width * index
    byte, shift = divmod(bit, 8)
    data = tables[table]
    return (int.from_bytes(data[byte:byte + (width + shift + 7) // 8], 'little') >> shift) & ((1 << width) - 1)


def raw_class(code):
    return lane('rawClass', 12, code)


STEPS = ((1, 0), (0, 1), (-1, 0), (0, -1))


def decode(code):
    return tuple((code >> (2 * (9 - i))) & 3 for i in range(10))


def encode(word):
    value = 0
    for d in word:
        value = 4 * value + d
    return value


def geometry(word):
    vertices = [(0, 0)]
    bonds = set()
    for d in word:
        x, y = vertices[-1]
        dx, dy = STEPS[d]
        nxt = (x + dx, y + dy)
        bond = frozenset((vertices[-1], nxt))
        if bond in bonds:
            return None
        bonds.add(bond)
        vertices.append(nxt)
    return vertices, bonds


def row(word):
    vertices, bonds = geometry(word)
    endpoint = vertices[-1]
    revisit = endpoint in vertices[:-1]
    entries = []
    for d, (dx, dy) in enumerate(STEPS):
        nxt = (endpoint[0] + dx, endpoint[1] + dy)
        allowed = d != (word[-1] + 2) % 4 and frozenset((endpoint, nxt)) not in bonds
        kind = 2 if revisit else (0 if d == word[-1] else 1)
        successor = encode(word[1:] + (d,))
        entries.append((allowed, kind, successor))
    return entries


# Independently generate exactly the distinct-unoriented-bond words in the paper.
raw_words = {}
depth_counts = Counter()


def generate(word=(), endpoint=(0, 0), used=frozenset(), code=0):
    if word:
        depth_counts[len(word)] += 1
    if len(word) == 10:
        raw_words[code] = word
        return
    for d, (dx, dy) in enumerate(STEPS):
        nxt = (endpoint[0] + dx, endpoint[1] + dy)
        bond = frozenset((endpoint, nxt))
        if bond not in used:
            generate(word + (d,), nxt, used | {bond}, 4 * code + d)


generate()
assert [depth_counts[i] for i in range(1, 11)] == [4, 12, 36, 108, 316, 916, 2628, 7500, 21268, 60092]

# Check the decoder's entire finite domain; invalid words must have sentinel 3741.
coverage_errors = []
class_counts = Counter()
for code in range(4 ** 10):
    a = raw_class(code)
    if a > 3741 or ((a < 3741) != (code in raw_words)):
        coverage_errors.append((code, a, code in raw_words))
    if code in raw_words:
        class_counts[a] += 1
assert not coverage_errors, coverage_errors[:10]
assert set(class_counts) == set(range(3741))

representatives = [lane('representatives', 20, a) for a in range(3741)]
rep_errors = []
edge_errors = []
edge_counts = Counter()
for a, code in enumerate(representatives):
    if code >= 4 ** 10 or code not in raw_words or raw_class(code) != a:
        rep_errors.append((a, code))
        continue
    for d, (allowed, kind, succ) in enumerate(row(decode(code))):
        destination = lane('destinations', 12, a * 4 + d)
        stored_kind = lane('edgeKinds', 2, a * 4 + d)
        if not (destination <= 3741 and ((destination == 0) == (stored_kind == 3))):
            edge_errors.append(('range/sentinel', a, d, destination, stored_kind))
        if bool(destination) != allowed:
            edge_errors.append(('allowed', a, d))
        if allowed:
            edge_counts[kind] += 1
            if stored_kind != kind or destination - 1 != raw_class(succ):
                edge_errors.append(('kind/successor', a, d))
assert not rep_errors, rep_errors[:10]
assert not edge_errors, edge_errors[:10]
assert [edge_counts[i] for i in range(3)] == [2516, 5032, 1872]

# Check the class map against representative geometry for every raw word, including
# the all-directions kind condition in the paper's quotient lemma.
quotient_errors = []
for code, word in raw_words.items():
    a = raw_class(code)
    rep_word = decode(representatives[a])
    for d, ((allowed, kind, succ), (r_allowed, r_kind, r_succ)) in enumerate(zip(row(word), row(rep_word))):
        if allowed != r_allowed or kind != r_kind:
            quotient_errors.append(('admissibility/kind', code, a, d))
        if allowed and (raw_class(succ) != raw_class(r_succ) or
                        (kind != 2 and word[-1] != rep_word[-1])):
            quotient_errors.append(('successor/arrival', code, a, d))
assert not quotient_errors, quotient_errors[:10]

result = {
    'method': 'Exact Python integers; source arithmetic parsed, independently generated lattice trails',
    'depth_counts': dict(sorted(depth_counts.items())),
    'whole_table_coverage_errors': len(coverage_errors),
    'representative_errors': len(rep_errors),
    'stored_edge_errors': len(edge_errors),
    'quotient_errors': len(quotient_errors),
    'edge_counts_straight_turn_revisit': [edge_counts[i] for i in range(3)],
    'assigned': [],
}
for i in range(325, 330):
    name = f'rawClass_{i}'
    lo = positions['rawClass'][name]
    hi = lo + 4 * (len(literal_hex[name]) - 2) - 1
    first, last = lo // 12, hi // 12
    codes = list(range(first, last + 1))
    valid = [code for code in codes if code in raw_words]
    result['assigned'].append({
        'name': name,
        'source_line': source[:source.index(f'private noncomputable def {name} :')].count('\n') + 1,
        'literal_sha256': hashlib.sha256(literal_hex[name].encode()).hexdigest(),
        'bit_range_inclusive': [lo, hi],
        'code_range_inclusive': [first, last],
        'codes_touching': len(codes),
        'valid_words': len(valid),
        'invalid_words': len(codes) - len(valid),
        'distinct_classes': len(set(raw_class(code) for code in valid)),
        'first_valid_examples': [
            {'code': code, 'word': ''.join('ENWS'[d] for d in raw_words[code]),
             'class': raw_class(code), 'representative': representatives[raw_class(code)]}
            for code in valid[:3]
        ],
        'coverage_and_quotient_errors': 0,
    })

Path('audit_results.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
