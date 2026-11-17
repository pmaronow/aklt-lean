"""Read-only finite audit of Automaton10Data, with focus on rawClass_180..184."""
from pathlib import Path
import ast
import collections
import hashlib
import json
import re

SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
s = SOURCE.read_text()
literals = {}
widths = {}
lines = {}
expressions = {}
for lineno, line in enumerate(s.splitlines(), 1):
    m = re.fullmatch(r'private noncomputable def (\w+) : ℕ := 0x([0-9a-f]+)', line)
    if m:
        name, h = m.groups()
        literals[name] = int(h, 16)
        widths[name] = 4 * len(h)
        lines[name] = lineno
    m = re.fullmatch(r'noncomputable def (\w+) : ℕ := (.+)', line)
    if m:
        expressions[m[1]] = m[2]

def evaluate(node):
    if isinstance(node, ast.Name):
        return literals[node.id], {node.id: 0}
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.LShift):
        assert isinstance(node.right, ast.Constant) and isinstance(node.right.value, int)
        val, offsets = evaluate(node.left)
        shift = node.right.value
        return val << shift, {k: v + shift for k, v in offsets.items()}
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add):
        left, lo = evaluate(node.left)
        right, ro = evaluate(node.right)
        assert not (lo.keys() & ro.keys())
        return left + right, lo | ro
    raise ValueError(ast.dump(node))

tables = {}
placements = {}
for name, expression in expressions.items():
    tree = ast.parse(expression.replace('<<<', '<<'), mode='eval')
    value, offsets = evaluate(tree.body)
    intervals = sorted((v, v + widths[k], k) for k, v in offsets.items())
    assert intervals[0][0] == 0
    assert all(a[1] == b[0] for a, b in zip(intervals, intervals[1:]))
    nbits = intervals[-1][1]
    assert value.bit_length() <= nbits
    tables[name] = value.to_bytes((nbits + 7) // 8, 'little')
    placements[name] = offsets

def lane(table, width, index):
    bit = width * index
    j, rem = divmod(bit, 8)
    nbytes = (rem + width + 7) // 8
    return (int.from_bytes(tables[table][j:j + nbytes], 'little') >> rem) & ((1 << width) - 1)

raw = [lane('rawClass', 12, code) for code in range(4**10)]
reps = [lane('representatives', 20, a) for a in range(3741)]
dests = [[lane('destinations', 12, 4*a+d) for d in range(4)] for a in range(3741)]
kinds = [[lane('edgeKinds', 2, 4*a+d) for d in range(4)] for a in range(3741)]
steps = [(1, 0), (0, 1), (-1, 0), (0, -1)]

def decode(code):
    return tuple((code >> (2*(9-i))) & 3 for i in range(10))

def state(word):
    x = y = 0
    vertices = [(x, y)]
    bonds = set()
    valid = True
    for d in word:
        dx, dy = steps[d]
        nxt = (x+dx, y+dy)
        bond = tuple(sorted(((x, y), nxt)))
        if bond in bonds:
            valid = False
        bonds.add(bond)
        x, y = nxt
        vertices.append(nxt)
    return vertices, bonds, valid

def row(code):
    word = decode(code)
    vertices, bonds, valid = state(word)
    assert valid
    end = vertices[-1]
    revisit = end in vertices[:-1]
    result = []
    for d, (dx, dy) in enumerate(steps):
        bond = tuple(sorted((end, (end[0]+dx, end[1]+dy))))
        allowed = d != (word[-1]+2) % 4 and bond not in bonds
        kind = 2 if revisit else (0 if d == word[-1] else 1)
        succ = ((code & (4**9-1)) << 2) + d
        result.append((allowed, kind, raw[succ] if allowed else None))
    return word[-1], result

# Generate exactly the mathematical raw set; no table values control generation.
valid_codes = set()
counts = collections.Counter()
def generate(depth, code, pos, bonds):
    counts[depth] += 1
    if depth == 10:
        valid_codes.add(code)
        return
    for d, step in enumerate(steps):
        nxt = (pos[0]+step[0], pos[1]+step[1])
        bond = tuple(sorted((pos, nxt)))
        if bond not in bonds:
            bonds.add(bond)
            generate(depth+1, 4*code+d, nxt, bonds)
            bonds.remove(bond)
generate(0, 0, (0, 0), set())
assert len(valid_codes) == 60092
coverage_errors = [code for code, a in enumerate(raw)
                   if a > 3741 or ((a < 3741) != (code in valid_codes))]
assert not coverage_errors, coverage_errors[:10]
assert all(0 <= code < 4**10 and code in valid_codes and raw[code] == a
           for a, code in enumerate(reps))
assert all(0 <= dests[a][d] <= 3741 and
           ((dests[a][d] == 0) == (kinds[a][d] == 3))
           for a in range(3741) for d in range(4))

# Compare every raw row with the designated stored quotient row and representative.
row_errors = []
rep_rows = [row(code) for code in reps]
for code in sorted(valid_codes):
    a = raw[code]
    arrival, transitions = row(code)
    rep_arrival, rep_transitions = rep_rows[a]
    for d, (allowed, kind, successor) in enumerate(transitions):
        stored_allowed = dests[a][d] != 0
        if allowed != stored_allowed:
            row_errors.append((code, a, d, 'admissibility'))
        if allowed and (kinds[a][d] != kind or dests[a][d]-1 != successor or
                        (kind != 2 and arrival != rep_arrival)):
            row_errors.append((code, a, d, 'kind/successor/arrival'))
        # The paper's quotient hypotheses also ask for identical raw kinds.
        if kind != rep_transitions[d][1]:
            row_errors.append((code, a, d, 'representative kind'))
assert not row_errors, row_errors[:10]
edge_counts = dict(collections.Counter(kinds[a][d] for a in range(3741)
                                     for d in range(4) if dests[a][d]))
assert edge_counts == {0: 2516, 1: 5032, 2: 1872}

focus = []
for i in range(180, 185):
    name = f'rawClass_{i}'
    offset = placements['rawClass'][name]
    assert offset == sum(widths[f'rawClass_{j}'] for j in range(i+1,768))
    first = offset // 12
    last = (offset + widths[name] - 1) // 12
    affected = range(first, last+1)
    valids = [c for c in affected if c in valid_codes]
    invalids = [c for c in affected if c not in valid_codes]
    # These include the boundary lanes assembled from two different chunks.
    assert all(raw[c] == 3741 for c in invalids)
    assert all(raw[c] < 3741 for c in valids)
    focus.append({
        'declaration': name, 'line': lines[name], 'bits': widths[name],
        'lsb_offset': offset, 'first_code': first, 'last_code': last,
        'start_bit_in_first_lane': offset % 12,
        'end_bit_in_last_lane_exclusive': (offset+widths[name]-1) % 12 + 1,
        'raw_windows': len(valids), 'invalid_words': len(invalids),
        'distinct_classes': len({raw[c] for c in valids}),
        'valid_samples': [(c, ''.join('ENWS'[d] for d in decode(c)), raw[c]) for c in valids[:3]],
        'boundary_lanes': [(c, raw[c], c in valid_codes) for c in (first, last)],
        'sha256_big_endian_bytes': hashlib.sha256(literals[name].to_bytes(2048,'big')).hexdigest(),
    })
result = {
    'literal_chunks': len(literals),
    'raw_class_chunks': len(placements['rawClass']),
    'raw_table_assembled_hex_bits': sum(widths[k] for k in placements['rawClass']),
    'raw_table_byte_capacity_bits': 8*len(tables['rawClass']),
    'raw_chunk_width_exceptions': {k: v for k, v in widths.items() if k.startswith('rawClass_') and v != 16384},
    'raw_coverage_errors': len(coverage_errors),
    'raw_word_counts_by_depth': dict(sorted(counts.items())),
    'class_representatives_checked': len(reps),
    'raw_rows_checked': len(valid_codes),
    'labelled_raw_directions_checked': 4*len(valid_codes),
    'row_errors': len(row_errors),
    'edge_counts': edge_counts,
    'focus': focus,
}
print(json.dumps(result, indent=2))
