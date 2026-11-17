"""Read-only reconstruction of the Lean literal tables and raw trail model."""

import ast
from collections import Counter
import json
from pathlib import Path
import re


SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
source = SOURCE.read_text()
literal_text = dict(re.findall(
    r'private noncomputable def (\w+) : ℕ := 0x([0-9a-f]+)', source))
literals = {name: int(h, 16) for name, h in literal_text.items()}


def evaluate(node):
    if isinstance(node, ast.Name):
        return literals[node.id], [(node.id, 0)]
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add):
        a, terms_a = evaluate(node.left)
        b, terms_b = evaluate(node.right)
        return a + b, terms_a + terms_b
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.LShift):
        a, terms = evaluate(node.left)
        assert isinstance(node.right, ast.Constant)
        shift = node.right.value
        return a << shift, [(name, offset + shift) for name, offset in terms]
    raise ValueError(ast.dump(node))


tables = {}
offsets = {}
for name in ['rawClass', 'representatives', 'destinations', 'edgeKinds']:
    expr = re.search(r'^noncomputable def ' + name + r' : ℕ := (.+)$',
                     source, re.M)[1]
    value, terms = evaluate(ast.parse(expr.replace('<<<', '<<'), mode='eval').body)
    expected = 0
    for chunk, offset in reversed(terms):
        assert offset == expected, (chunk, offset, expected)
        expected += len(literal_text[chunk]) * 4
        offsets[chunk] = offset
    assert [chunk for chunk, _ in terms] == [f'{name}_{i}' for i in range(len(terms))]
    tables[name] = value.to_bytes((value.bit_length() + 7) // 8, 'little')


def lane(table, width, index):
    bit = width * index
    start, shift = divmod(bit, 8)
    count = (width + shift + 7) // 8
    return (int.from_bytes(tables[table][start:start + count], 'little') >> shift) & ((1 << width) - 1)


N = 4**10
raw_class = [lane('rawClass', 12, code) for code in range(N)]
reps = [lane('representatives', 20, a) for a in range(3741)]
dest = [[lane('destinations', 12, 4*a+d) for d in range(4)] for a in range(3741)]
kinds = [[lane('edgeKinds', 2, 4*a+d) for d in range(4)] for a in range(3741)]
steps = [(1, 0), (0, 1), (-1, 0), (0, -1)]


def decode(code):
    return [(code // 4**(9-i)) % 4 for i in range(10)]


def encode(word):
    return sum(d * 4**(9-i) for i, d in enumerate(word))


def bond(x, y):
    return tuple(sorted((x, y)))


def geometry(word):
    vertices = [(0, 0)]
    bonds = []
    for d in word:
        x, y = vertices[-1]
        dx, dy = steps[d]
        nxt = (x+dx, y+dy)
        bonds.append(bond(vertices[-1], nxt))
        vertices.append(nxt)
    return vertices, bonds


windows = {}
counts = []


def generate(depth, code, word, vertices, used):
    if depth == 10:
        windows[code] = (word, vertices, used)
        return
    x, y = vertices[-1]
    for d, (dx, dy) in enumerate(steps):
        nxt = (x+dx, y+dy)
        edge = bond(vertices[-1], nxt)
        if edge not in used:
            counts[depth] += 1
            generate(depth+1, 4*code+d, word+[d], vertices+[nxt], used | {edge})


counts = [0]*10
generate(0, 0, [], [(0, 0)], set())
assert counts == [4, 12, 36, 108, 316, 916, 2628, 7500, 21268, 60092]

coverage_errors = [code for code, a in enumerate(raw_class)
                   if a > 3741 or ((a < 3741) != (code in windows))]
rep_errors = []
for a, code in enumerate(reps):
    if not (code < N and code in windows and raw_class[code] == a):
        rep_errors.append((a, code, raw_class[code]))
row_encoding_errors = []
for a in range(3741):
    for d in range(4):
        if dest[a][d] > 3741 or ((dest[a][d] == 0) != (kinds[a][d] == 3)):
            row_encoding_errors.append((a, d))


def actual_row(word, vertices, used):
    last = word[-1]
    x, y = vertices[-1]
    revisit = vertices[-1] in vertices[:-1]
    row = []
    for d, (dx, dy) in enumerate(steps):
        allowed = d != (last + 2) % 4 and bond((x, y), (x+dx, y+dy)) not in used
        kind = 2 if revisit else (0 if d == last else 1)
        successor = (encode(word[1:] + [d])) if allowed else None
        row.append((allowed, kind, successor))
    return row


row_errors = []
representative_kind_errors = []
raw_edge_counts = Counter()
rows = {}
rep_rows = [actual_row(*windows[code]) for code in reps]
for code, (word, vertices, used) in windows.items():
    assert decode(code) == word
    assert geometry(word) == (vertices, [bond(vertices[i], vertices[i+1]) for i in range(10)])
    a = raw_class[code]
    row = actual_row(word, vertices, used)
    rows[code] = row
    for d, (allowed, kind, successor) in enumerate(row):
        errors = []
        if kind != rep_rows[a][d][1]:
            representative_kind_errors.append((code, a, d))
        if allowed != (dest[a][d] != 0):
            errors.append('admissibility')
        if allowed:
            raw_edge_counts[kind] += 1
            if kinds[a][d] != kind:
                errors.append('kind')
            if successor not in windows:
                errors.append('successor-not-raw')
            if (max(dest[a][d]-1, 0) % 3741) != raw_class[successor]:
                errors.append('successor-class')
            if kind != 2 and reps[a] % 4 != word[-1]:
                errors.append('arrival')
        if errors:
            row_errors.append({'code': code, 'class': a, 'direction': d, 'errors': errors})

class_edge_counts = Counter(kinds[a][d] for a in range(3741)
                            for d in range(4) if dest[a][d] != 0)
target_results = []
for j in range(185, 190):
    name = f'rawClass_{j}'
    lo = offsets[name]
    hi = lo + 4*len(literal_text[name]) - 1
    first, last = lo // 12, hi // 12
    codes = list(range(first, last+1))
    valid = [code for code in codes if code in windows]
    edges = Counter(kind for code in valid for allowed, kind, _ in rows[code] if allowed)
    classes = sorted({raw_class[code] for code in valid})
    target_results.append({
        'declaration': name,
        'source_line': next(i for i, line in enumerate(source.splitlines(), 1)
                            if line.startswith('private noncomputable def '+name+' ')),
        'bit_range_inclusive': [lo, hi],
        'intersecting_code_range_inclusive': [first, last],
        'intersecting_codes': len(codes),
        'raw_codes': len(valid),
        'invalid_codes': len(codes)-len(valid),
        'distinct_classes': len(classes),
        'admissible_edges_by_kind': dict(sorted(edges.items())),
        'coverage_errors': [code for code in coverage_errors if first <= code <= last],
        'row_errors': [e for e in row_errors if first <= e['code'] <= last],
        'first_valid_examples': [{'code': code, 'directions': ''.join('ENWS'[d] for d in windows[code][0]),
                                  'class': raw_class[code], 'representative': reps[raw_class[code]]}
                                 for code in valid[:3]],
        'boundary_lanes': [{'code': code, 'class_or_sentinel': raw_class[code]} for code in [first, last]],
    })

result = {
    'raw_counts_by_length': counts,
    'all_code_coverage_errors': len(coverage_errors),
    'all_representative_errors': rep_errors,
    'all_row_encoding_errors': row_encoding_errors,
    'all_raw_row_errors': row_errors,
    'all_representative_kind_errors_including_inadmissible_directions': representative_kind_errors,
    'class_edge_counts_by_kind': dict(sorted(class_edge_counts.items())),
    'raw_admissible_edge_counts_by_kind': dict(sorted(raw_edge_counts.items())),
    'targets': target_results,
}
Path('audit_results.json').write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps(result, indent=2))
