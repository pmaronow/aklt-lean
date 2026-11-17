"""Independent finite reconstruction of the supplied automaton's literal data.

Reads only the assigned Lean input. Does not use an archived automaton file.
"""
import ast
from collections import Counter
import hashlib
import json
from pathlib import Path
import re

SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
source = SOURCE.read_text()
chunks = {}
line_numbers = {}
for number, line in enumerate(source.splitlines(), 1):
    match = re.fullmatch(r'private noncomputable def (\w+) : ℕ := (0x[0-9a-fA-F]+)', line)
    if match:
        chunks[match[1]] = int(match[2], 16)
        line_numbers[match[1]] = number


def evaluate(node):
    if isinstance(node, ast.Name):
        return chunks[node.id]
    if isinstance(node, ast.Constant) and isinstance(node.value, int):
        return node.value
    if isinstance(node, ast.BinOp):
        left, right = evaluate(node.left), evaluate(node.right)
        if isinstance(node.op, ast.Add):
            return left + right
        if isinstance(node.op, ast.LShift):
            return left << right
    raise ValueError(ast.dump(node))


trees = {}
packed = {}
for name in ('rawClass', 'representatives', 'destinations', 'edgeKinds'):
    expression = re.search(r'^noncomputable def ' + name + r' : ℕ := (.+)$', source, re.M)[1]
    trees[name] = ast.parse(expression.replace('<<<', '<<'), mode='eval').body
    packed[name] = evaluate(trees[name])


def terms(node, offset=0):
    if isinstance(node, ast.Name):
        return [(node.id, offset)]
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add):
        return terms(node.left, offset) + terms(node.right, offset)
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.LShift):
        return terms(node.left, offset + evaluate(node.right))
    raise ValueError(ast.dump(node))


raw_terms = terms(trees['rawClass'])
assert [name for name, _ in raw_terms] == [f'rawClass_{i}' for i in range(768)]
by_offset = sorted(raw_terms, key=lambda t: t[1])
assert by_offset[0][1] == 0
for (name, offset), (_, next_offset) in zip(by_offset, by_offset[1:]):
    assert chunks[name].bit_length() <= next_offset - offset

N = 4**10
Q = 3741
raw_hex = format(packed['rawClass'], f'0{3*N}x')
assert len(raw_hex) == 3*N
raw = [int(raw_hex[3*(N-1-code):3*(N-code)], 16) for code in range(N)]


def lane(name, width, index):
    return (packed[name] >> (width*index)) % (1 << width)


reps = [lane('representatives', 20, a) for a in range(Q)]
dest = [[lane('destinations', 12, 4*a+d) for d in range(4)] for a in range(Q)]
kinds = [[lane('edgeKinds', 2, 4*a+d) for d in range(4)] for a in range(Q)]
steps = ((1, 0), (0, 1), (-1, 0), (0, -1))
counts = [0]*11
windows = {}


def generate(word, code, vertices, bonds):
    depth = len(word)
    counts[depth] += 1
    if depth == 10:
        windows[code] = (word, vertices, bonds)
        return
    x, y = vertices[-1]
    for d, (dx, dy) in enumerate(steps):
        endpoint = (x+dx, y+dy)
        bond = tuple(sorted(((x, y), endpoint)))
        if bond not in bonds:
            generate(word+(d,), 4*code+d, vertices+(endpoint,), bonds | {bond})


generate((), 0, ((0, 0),), frozenset())
assert counts[1:] == [4, 12, 36, 108, 316, 916, 2628, 7500, 21268, 60092]
coverage_errors = [code for code, a in enumerate(raw) if a > Q or ((a < Q) != (code in windows))]
assert not coverage_errors, coverage_errors[:10]
assert set(raw[code] for code in windows) == set(range(Q))
assert all(code < N and code in windows and raw[code] == a for a, code in enumerate(reps))
assert all(0 <= v <= Q for row in dest for v in row)
assert all((dest[a][d] == 0) == (kinds[a][d] == 3) for a in range(Q) for d in range(4))

transition_errors = []
checked_admitted = 0
for code, (word, vertices, bonds) in windows.items():
    a = raw[code]
    current = vertices[-1]
    revisit = current in vertices[:-1]
    for d, (dx, dy) in enumerate(steps):
        new = (current[0]+dx, current[1]+dy)
        bond = tuple(sorted((current, new)))
        admitted = d != (word[-1]+2) % 4 and bond not in bonds
        kind = 2 if revisit else (0 if d == word[-1] else 1)
        if (dest[a][d] != 0) != admitted:
            transition_errors.append(('allowed', code, a, d))
        if admitted:
            checked_admitted += 1
            successor = 4*(code % 4**9)+d
            if successor not in windows or dest[a][d]-1 != raw[successor]:
                transition_errors.append(('successor', code, a, d))
            if kinds[a][d] != kind:
                transition_errors.append(('kind', code, a, d))
            if kind != 2 and reps[a] % 4 != word[-1]:
                transition_errors.append(('arrival', code, a, d))
        # Compare kinds of raw words with their representative even on forbidden
        # labels, as the quotient lemma's premise says, independently of the
        # forbidden-label sentinel in the stored kind table.
        rep_word, rep_vertices, _ = windows[reps[a]]
        rep_kind = 2 if rep_vertices[-1] in rep_vertices[:-1] else (0 if d == rep_word[-1] else 1)
        if rep_kind != kind:
            transition_errors.append(('representative_kind', code, a, d))
assert not transition_errors, transition_errors[:10]
edge_counts = Counter(kinds[a][d] for a in range(Q) for d in range(4) if dest[a][d])
assert edge_counts == Counter({0: 2516, 1: 5032, 2: 1872})

summary = {
    'source_sha256': hashlib.sha256(source.encode()).hexdigest(),
    'literal_chunks_read': len(chunks),
    'raw_chunks': len(raw_terms),
    'raw_packed_bit_length': packed['rawClass'].bit_length(),
    'raw_counts_depth_0_to_10': counts,
    'raw_class_histogram_summary': {'valid': len(windows), 'sentinel_3741': raw.count(Q), 'other_invalid': sum(a > Q for a in raw)},
    'raw_projection_surjective': True,
    'all_representatives_valid_and_project_to_own_class': True,
    'raw_direction_pairs_checked': 4*len(windows),
    'admitted_raw_edges_checked': checked_admitted,
    'coverage_errors': len(coverage_errors),
    'transition_errors': len(transition_errors),
    'quotient_edge_counts_straight_turn_revisit': [edge_counts[k] for k in range(3)],
    'targets': [],
}
offsets = dict(raw_terms)
for index in range(150, 155):
    name = f'rawClass_{index}'
    offset = offsets[name]
    width = 16384
    assert chunks[name].bit_length() <= width
    assert ((packed['rawClass'] >> offset) % (1 << width)) == chunks[name]
    first, last = offset // 12, (offset+width-1) // 12
    affected = range(first, last+1)
    valid = [code for code in affected if code in windows]
    class_values = [raw[code] for code in valid]
    target = {
        'name': name, 'line': line_numbers[name], 'bit_offset': offset, 'reserved_bits': width,
        'hex_digits': len(format(chunks[name], 'x')),
        'sha256_of_hex_digits': hashlib.sha256(format(chunks[name], 'x').encode()).hexdigest(),
        'affected_codes_inclusive': [first, last],
        'fully_contained_codes_inclusive': [(offset+11)//12, (offset+width)//12-1],
        'partial_lane_codes': [code for code in affected if 12*code < offset or 12*(code+1) > offset+width],
        'affected_code_count': len(affected),
        'valid_raw_words': len(valid), 'invalid_sentinel_words': len(affected)-len(valid),
        'valid_class_range': [min(class_values), max(class_values)] if valid else None,
        'first_valid_sample': {'code': valid[0], 'word': ''.join('ENWS'[d] for d in windows[valid[0]][0]), 'class': raw[valid[0]]} if valid else None,
    }
    summary['targets'].append(target)

print(json.dumps(summary, indent=2))
