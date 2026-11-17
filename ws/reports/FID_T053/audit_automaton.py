"""Read-only reconstruction of the paper's memory-ten automaton contract."""
from collections import Counter
from pathlib import Path
import json
import re

SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
TEXT = SOURCE.read_text()
Q = 3741
M = 10
STEPS = ((1, 0), (0, 1), (-1, 0), (0, -1))
TARGETS = range(230, 235)
LITERALS = {}
LINES = {}
for lineno, line in enumerate(TEXT.splitlines(), 1):
    match = re.fullmatch(r'private noncomputable def (\w+) : ℕ := 0x([0-9a-f]+)', line)
    if match:
        name, digits = match.groups()
        LITERALS[name] = (int(digits, 16), 4 * len(digits))
        LINES[name] = lineno


def parse_packed(name):
    """Evaluate the actual parenthesized Lean shifts/additions; track all leaves."""
    expression = re.search(r'^noncomputable def ' + name + r' : ℕ := (.+)$', TEXT, re.M).group(1)
    tokens = re.findall(r'<<<|[()+]|\w+', expression)
    position = 0

    def atom():
        nonlocal position
        token = tokens[position]
        position += 1
        if token == '(':
            result = expression_value()
            assert tokens[position] == ')'
            position += 1
            return result
        value, width = LITERALS[token]
        return value, [(token, 0, width)]

    def shifted():
        nonlocal position
        value, leaves = atom()
        if position < len(tokens) and tokens[position] == '<<<':
            amount = int(tokens[position + 1])
            position += 2
            value <<= amount
            leaves = [(key, offset + amount, width) for key, offset, width in leaves]
        return value, leaves

    def expression_value():
        nonlocal position
        value, leaves = shifted()
        while position < len(tokens) and tokens[position] == '+':
            position += 1
            other, other_leaves = shifted()
            value += other
            leaves += other_leaves
        return value, leaves

    value, leaves = expression_value()
    assert position == len(tokens)
    assert len({key for key, _, _ in leaves}) == len(leaves)
    ordered = sorted(leaves, key=lambda leaf: leaf[1])
    assert ordered[0][1] == 0
    assert all(a[1] + a[2] == b[1] for a, b in zip(ordered, ordered[1:]))
    return value, {key: (offset, width) for key, offset, width in leaves}


def lanes(value, width, count):
    data = value.to_bytes((value.bit_length() + 7) // 8, 'little')
    mask = (1 << width) - 1
    return [
        (int.from_bytes(data[(width*i)//8:(width*i+width+7)//8], 'little')
         >> ((width*i) % 8)) & mask
        for i in range(count)
    ]


raw_packed, offsets = parse_packed('rawClass')
rep_packed, _ = parse_packed('representatives')
dest_packed, _ = parse_packed('destinations')
kind_packed, _ = parse_packed('edgeKinds')
raw = lanes(raw_packed, 12, 4**M)
reps = lanes(rep_packed, 20, Q)
dests = lanes(dest_packed, 12, 4*Q)
kinds = lanes(kind_packed, 2, 4*Q)


def decode(code):
    return tuple((code >> (2*(M-1-i))) & 3 for i in range(M))


def edge(x, y):
    return tuple(sorted((x, y)))


def geometry(word):
    vertices = [(0, 0)]
    bonds = set()
    for d in word:
        x = vertices[-1]
        dx, dy = STEPS[d]
        y = (x[0] + dx, x[1] + dy)
        bonds.add(edge(x, y))
        vertices.append(y)
    return vertices, bonds


counts = [0] * (M+1)
valid = set()


def generate(depth, code, x, used):
    counts[depth] += 1
    if depth == M:
        valid.add(code)
        return
    for d, (dx, dy) in enumerate(STEPS):
        y = (x[0]+dx, x[1]+dy)
        bond = edge(x, y)
        if bond not in used:
            used.add(bond)
            generate(depth+1, code*4+d, y, used)
            used.remove(bond)


generate(0, 0, (0, 0), set())
coverage_errors = [code for code, a in enumerate(raw) if a > Q or ((a < Q) != (code in valid))]
rep_errors = [a for a, code in enumerate(reps) if code >= 4**M or code not in valid or raw[code] != a]
row_encoding_errors = [i for i in range(4*Q)
                       if dests[i] > Q or ((dests[i] == 0) != (kinds[i] == 3))
                       or (dests[i] != 0 and kinds[i] >= 3)]
errors = Counter()
examples = {}
rep_words = [decode(code) for code in reps]
rep_geometries = [geometry(word) for word in rep_words]


def record(category, code, d, **details):
    errors[category] += 1
    examples.setdefault(category, dict(code=code, direction=d, **details))


for code in sorted(valid):
    word = decode(code)
    vertices, bonds = geometry(word)
    a = raw[code]
    if not 0 <= a < Q:
        record('raw_class_range', code, None, value=a)
        continue
    rep_word = rep_words[a]
    rep_vertices, rep_bonds = rep_geometries[a]
    revisiting = vertices[-1] in vertices[:-1]
    rep_revisiting = rep_vertices[-1] in rep_vertices[:-1]
    for d, (dx, dy) in enumerate(STEPS):
        y = (vertices[-1][0]+dx, vertices[-1][1]+dy)
        allowed = d != (word[-1]+2) % 4 and edge(vertices[-1], y) not in bonds
        k = 2 if revisiting else (0 if d == word[-1] else 1)
        rep_k = 2 if rep_revisiting else (0 if d == rep_word[-1] else 1)
        row = 4*a+d
        if allowed != (dests[row] != 0):
            record('admissibility', code, d, a=a)
        if k != rep_k:
            record('kind_compatibility_all_directions', code, d, a=a)
        if allowed:
            if kinds[row] != k:
                record('kind', code, d, a=a, actual=kinds[row], expected=k)
            next_code = (code % (4**(M-1)))*4+d
            if next_code not in valid or dests[row] != raw[next_code]+1:
                record('successor', code, d, a=a, successor_code=next_code)
            if k != 2 and word[-1] != rep_word[-1]:
                record('arrival', code, d, a=a)


target_results = {}
for i in TARGETS:
    name = f'rawClass_{i}'
    offset, width = offsets[name]
    lo, hi = offset//12, (offset+width-1)//12
    full_lo, full_hi = (offset+11)//12, (offset+width)//12-1
    affected = range(lo, hi+1)
    raw_codes = [c for c in affected if c in valid]
    target_results[name] = {
        'source_line': LINES[name], 'bit_offset': offset, 'width_bits': width,
        'affected_codes_inclusive': [lo, hi],
        'whole_lanes_codes_inclusive': [full_lo, full_hi],
        'partial_boundary_codes': [c for c in affected if c < full_lo or c > full_hi],
        'affected_raw_words': len(raw_codes),
        'affected_invalid_words': len(affected)-len(raw_codes),
        'affected_class_range': [min((raw[c] for c in raw_codes), default=None),
                                 max((raw[c] for c in raw_codes), default=None)],
        'coverage_errors': [c for c in coverage_errors if lo <= c <= hi],
        'first_raw_examples': [{'code': c, 'word': ''.join('ENWS'[d] for d in decode(c)),
                                'class': raw[c], 'representative_code': reps[raw[c]]}
                               for c in raw_codes[:3]],
    }

result = {
    'source': str(SOURCE), 'literal_count': len(LITERALS),
    'raw_chunks': len(offsets), 'raw_bit_length': raw_packed.bit_length(),
    'raw_window_counts_by_depth': counts,
    'raw_code_count': len(valid), 'raw_class_range': [min(raw), max(raw)],
    'represented_classes': len({raw[c] for c in valid}),
    'coverage_error_count': len(coverage_errors), 'coverage_error_examples': coverage_errors[:3],
    'representative_error_count': len(rep_errors), 'representative_error_examples': rep_errors[:3],
    'row_encoding_error_count': len(row_encoding_errors),
    'regeneration_errors': dict(errors), 'regeneration_error_examples': examples,
    'labelled_edge_counts_by_kind': dict(sorted(Counter(kinds[i] for i in range(4*Q) if dests[i]).items())),
    'targets': target_results,
}
Path('audit-results.json').write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps(result, indent=2))
assert not coverage_errors and not rep_errors and not row_encoding_errors and not errors
assert counts[1:] == [4,12,36,108,316,916,2628,7500,21268,60092]
assert result['labelled_edge_counts_by_kind'] == {0:2516,1:5032,2:1872}
