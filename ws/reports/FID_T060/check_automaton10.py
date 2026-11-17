"""Independent integer decoding and paper-rule reconstruction; reads only Lean inputs."""
from pathlib import Path
from collections import Counter
import json
import re

INPUT = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
TEXT = INPUT.read_text()
LITERALS = {
    name: int(digits, 16)
    for name, digits in re.findall(
        r'^private noncomputable def (\w+) : ℕ := 0x([0-9a-fA-F]+)$', TEXT, re.M)
}


def parse(expression):
    tokens = re.findall(r'<<<|\w+|[()+]', expression)
    pos = 0

    def expr(min_precedence=0):
        nonlocal pos
        token = tokens[pos]
        pos += 1
        if token == '(':
            left = expr()
            assert tokens[pos] == ')'
            pos += 1
        else:
            left = int(token) if token.isdecimal() else token
        while pos < len(tokens) and tokens[pos] in ('+', '<<<'):
            op = tokens[pos]
            precedence = {'+': 60, '<<<': 65}[op]
            if precedence < min_precedence:
                break
            pos += 1
            right = expr(precedence + 1)
            left = (op, left, right)
        return left

    result = expr()
    assert pos == len(tokens), (pos, len(tokens))
    return result


def parts(tree, offset=0):
    if isinstance(tree, str):
        return [(tree, offset)]
    op, left, right = tree
    if op == '+':
        return parts(left, offset) + parts(right, offset)
    assert op == '<<<' and isinstance(right, int)
    return parts(left, offset + right)


def packed(name):
    expression = re.search(
        rf'^noncomputable def {name} : ℕ := (.*)$', TEXT, re.M).group(1)
    components = parts(parse(expression))
    assert len({n for n, _ in components}) == len(components)
    ordered = sorted(components, key=lambda p: p[1])
    assert ordered[0][1] == 0
    # Addition is bitwise concatenation: no literal spills into its neighbour.
    for (lower, lo), (_, hi) in zip(ordered, ordered[1:]):
        assert LITERALS[lower] < 2 ** (hi - lo), (lower, lo, hi)
    value = sum(LITERALS[n] << offset for n, offset in components)
    return value, dict(components)


RAW, OFFSETS = packed('rawClass')
REPS, _ = packed('representatives')
DESTS, _ = packed('destinations')
KINDS, _ = packed('edgeKinds')


def lanes(value, width, count):
    """Decode little-endian fixed-width lanes without repeated giant shifts."""
    bit_count = width * count
    assert value.bit_length() <= bit_count
    data = value.to_bytes((bit_count + 7) // 8, 'little')
    mask = (1 << width) - 1
    return [
        (int.from_bytes(data[(i * width) // 8:(i * width + width + 7) // 8], 'little')
         >> ((i * width) % 8)) & mask
        for i in range(count)
    ]


CLASS = lanes(RAW, 12, 4**10)
REP = lanes(REPS, 20, 3741)
DEST = lanes(DESTS, 12, 3741 * 4)
KIND = lanes(KINDS, 2, 3741 * 4)
STEP = [(1, 0), (0, 1), (-1, 0), (0, -1)]


def decode(code):
    return tuple((code >> (2 * (9 - i))) & 3 for i in range(10))


def encode(word):
    code = 0
    for d in word:
        code = code * 4 + d
    return code


def geometry(word):
    vertices = [(0, 0)]
    bonds = set()
    for d in word:
        x, y = vertices[-1]
        dx, dy = STEP[d]
        endpoint = (x + dx, y + dy)
        bond = frozenset((vertices[-1], endpoint))
        if bond in bonds:
            return None
        bonds.add(bond)
        vertices.append(endpoint)
    return vertices, bonds


def row(word):
    vertices, bonds = geometry(word)
    endpoint = vertices[-1]
    revisit = endpoint in vertices[:-1]
    result = []
    for d, (dx, dy) in enumerate(STEP):
        next_vertex = (endpoint[0] + dx, endpoint[1] + dy)
        allowed = d != (word[-1] + 2) % 4 and frozenset((endpoint, next_vertex)) not in bonds
        kind = 2 if revisit else 0 if d == word[-1] else 1
        successor = encode(word[1:] + (d,))
        result.append((allowed, kind, successor))
    return result


def generate():
    """Paper's recursion: all fresh unoriented bonds, with no virtual incoming bond."""
    counts = [0] * 11
    raw = {}

    def visit(word, code, vertices, bonds):
        depth = len(word)
        counts[depth] += 1
        if depth == 10:
            raw[code] = word
            return
        x, y = vertices[-1]
        for d, (dx, dy) in enumerate(STEP):
            endpoint = (x + dx, y + dy)
            bond = frozenset(((x, y), endpoint))
            if bond not in bonds:
                visit(word + (d,), code * 4 + d, vertices + (endpoint,), bonds | {bond})

    visit((), 0, ((0, 0),), set())
    return counts, raw


COUNTS, WINDOWS = generate()
ERRORS = Counter()
EXAMPLES = {}


def check(condition, category, detail):
    if not condition:
        ERRORS[category] += 1
        EXAMPLES.setdefault(category, detail)


for code, cls in enumerate(CLASS):
    check(cls <= 3741, 'raw_class_bound', (code, cls))
    check((cls < 3741) == (code in WINDOWS), 'raw_coverage', (code, cls))

for a, code in enumerate(REP):
    check(code < 4**10, 'representative_code_bound', (a, code))
    check(code in WINDOWS, 'representative_raw', (a, code))
    check(CLASS[code] == a, 'representative_section', (a, code, CLASS[code]))

EDGES = Counter()
for code, word in WINDOWS.items():
    a = CLASS[code]
    if a >= 3741:
        continue
    rep_word = decode(REP[a])
    rep_row = row(rep_word)
    for d, (allowed, kind, successor) in enumerate(row(word)):
        stored_dest, stored_kind = DEST[a * 4 + d], KIND[a * 4 + d]
        check(stored_dest <= 3741, 'destination_bound', (code, a, d, stored_dest))
        check((stored_dest == 0) == (stored_kind == 3), 'absent_encoding', (code, a, d))
        check((stored_dest != 0) == allowed, 'admissibility', (code, a, d))
        check(kind == rep_row[d][1], 'kind_vs_representative_all_directions', (code, a, d))
        if allowed:
            check(stored_kind == kind, 'kind', (code, a, d, stored_kind, kind))
            check(successor in WINDOWS, 'successor_raw', (code, a, d))
            check(stored_dest == CLASS[successor] + 1, 'successor_class',
                  (code, a, d, stored_dest, CLASS[successor]))
            if kind != 2:
                check(word[-1] == rep_word[-1], 'nonrevisit_arrival', (code, a, d))

for a, code in enumerate(REP):
    for d in range(4):
        if DEST[a * 4 + d] != 0:
            EDGES[KIND[a * 4 + d]] += 1

TARGETS = []
for k in range(265, 270):
    name = f'rawClass_{k}'
    start = OFFSETS[name]
    next_starts = [off for off in OFFSETS.values() if off > start]
    end = min(next_starts) if next_starts else 12 * 4**10
    first, last = start // 12, (end - 1) // 12
    touched = range(first, last + 1)
    valid = [code for code in touched if code in WINDOWS]
    target = {
        'name': name,
        'lean_line': next(i for i, line in enumerate(TEXT.splitlines(), 1)
                          if line.startswith(f'private noncomputable def {name} ')),
        'bit_start': start,
        'bit_end_exclusive': end,
        'literal_bit_length': LITERALS[name].bit_length(),
        'first_code': first,
        'last_code': last,
        'start_within_lane': start % 12,
        'end_within_lane': end % 12,
        'touched_lanes': len(touched),
        'raw_lanes': len(valid),
        'invalid_lanes': len(touched) - len(valid),
        'class_count': len({CLASS[code] for code in valid}),
        'valid_first_last': [(code, CLASS[code], ''.join('ENWS'[d] for d in WINDOWS[code]))
                             for code in (valid[:1] + valid[-1:])],
        'boundary_lanes': [(code, CLASS[code], code in WINDOWS)
                           for code in (first, last)],
    }
    TARGETS.append(target)

RESULT = {
    'method': 'Exact natural arithmetic; parsed every literal and complete concatenation AST; '
              'fresh-bond recursive generation from paper; exhaustive raw and quotient comparisons.',
    'literal_count': len(LITERALS),
    'packed_bit_lengths': {name: value.bit_length() for name, value in
                           [('rawClass', RAW), ('representatives', REPS),
                            ('destinations', DESTS), ('edgeKinds', KINDS)]},
    'raw_counts_depth_0_to_10': COUNTS,
    'all_code_count': len(CLASS),
    'stored_valid_raw_count': sum(a < 3741 for a in CLASS),
    'surjective_class_count': len({CLASS[code] for code in WINDOWS}),
    'edge_counts_kind_0_1_2': dict(EDGES),
    'errors': dict(ERRORS),
    'first_error_examples': EXAMPLES,
    'targets': TARGETS,
}
print(json.dumps(RESULT, indent=2))
Path('check_results.json').write_text(json.dumps(RESULT, indent=2) + '\n')
assert not ERRORS, (ERRORS, EXAMPLES)
assert COUNTS[1:] == [4, 12, 36, 108, 316, 916, 2628, 7500, 21268, 60092]
assert EDGES == {0: 2516, 1: 5032, 2: 1872}
