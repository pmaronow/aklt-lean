"""Independent arithmetic/trail audit of the permitted Lean literal input."""
from pathlib import Path
from collections import Counter
import json
import re

SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
text = SOURCE.read_text()
literals = {
    name: value
    for name, value in re.findall(
        r'private noncomputable def (\w+) : ℕ := (0x[0-9a-fA-F]+)', text
    )
}


def assemble(name):
    """Parse the actual assembly expression; shifts bind more tightly than +."""
    expression = re.search(r'noncomputable def ' + name + r' : ℕ := (.*)', text)[1]
    tokens = re.findall(r'<<<|\w+|[()+]', expression)
    pos = 0

    def atom():
        nonlocal pos
        token = tokens[pos]
        pos += 1
        if token == '(':
            value = add()
            assert tokens[pos] == ')'
            pos += 1
            return value
        if token.isdecimal():
            return int(token), []
        return int(literals[token], 16), [(token, 0, 4 * (len(literals[token]) - 2))]

    def shift():
        nonlocal pos
        value, pieces = atom()
        while pos < len(tokens) and tokens[pos] == '<<<':
            pos += 1
            count, empty = atom()
            assert not empty
            value <<= count
            pieces = [(n, o + count, w) for n, o, w in pieces]
        return value, pieces

    def add():
        nonlocal pos
        value, pieces = shift()
        while pos < len(tokens) and tokens[pos] == '+':
            pos += 1
            other, other_pieces = shift()
            assert value & other == 0, 'overlapping nonzero bits'
            value += other
            pieces += other_pieces
        return value, pieces

    value, pieces = add()
    assert pos == len(tokens)
    ordered = sorted(pieces, key=lambda p: p[1])
    assert ordered[0][1] == 0
    for a, b in zip(ordered, ordered[1:]):
        assert a[1] + a[2] == b[1], 'gap or overlapping chunk widths'
    return value, pieces


raw, raw_pieces = assemble('rawClass')
representatives, _ = assemble('representatives')
destinations, _ = assemble('destinations')
kinds, _ = assemble('edgeKinds')
# A three-hex-digit lane is exactly twelve bits. Avoid repeated huge shifts.
raw_hex = format(raw, 'x').zfill(3 * 4**10)
assert len(raw_hex) == 3 * 4**10
classes = [int(raw_hex[j:j+3], 16) for j in range(len(raw_hex)-3, -1, -3)]
reps = [(representatives >> (20 * a)) & (2**20-1) for a in range(3741)]
dest = [[(destinations >> (12 * (4*a+d))) & 4095 for d in range(4)] for a in range(3741)]
kind = [[(kinds >> (2 * (4*a+d))) & 3 for d in range(4)] for a in range(3741)]
steps = [(1, 0), (0, 1), (-1, 0), (0, -1)]


def decode(code):
    return [(code >> (2 * (9-i))) & 3 for i in range(10)]


def bond(a, b):
    return tuple(sorted((a, b)))


def reconstruct(code):
    ds = decode(code)
    vertices = [(0, 0)]
    bonds = set()
    for d in ds:
        x, y = vertices[-1]
        dx, dy = steps[d]
        endpoint = x+dx, y+dy
        edge = bond(vertices[-1], endpoint)
        if edge in bonds:
            return None
        bonds.add(edge)
        vertices.append(endpoint)
    final = vertices[-1]
    revisit = final in vertices[:-1]
    rows = []
    for d, (dx, dy) in enumerate(steps):
        admissible = d != (ds[-1]+2) % 4 and bond(final, (final[0]+dx, final[1]+dy)) not in bonds
        k = 2 if revisit else (0 if d == ds[-1] else 1)
        successor = ((code % 4**9) * 4 + d)
        rows.append((admissible, k, successor))
    return ds[-1], rows


# Generate the exact raw domain independently, retaining lexicographic code order.
valid = {}
counts = [0] * 11


def generate(depth, code, vertices, bonds):
    counts[depth] += 1
    if depth == 10:
        valid[code] = reconstruct(code)
        return
    start = vertices[-1]
    for d, (dx, dy) in enumerate(steps):
        endpoint = start[0]+dx, start[1]+dy
        edge = bond(start, endpoint)
        if edge not in bonds:
            generate(depth+1, 4*code+d, vertices+[endpoint], bonds | {edge})


generate(0, 0, [(0, 0)], set())
issues = Counter()
examples = {}


def issue(label, detail):
    issues[label] += 1
    examples.setdefault(label, detail)


for code, cls in enumerate(classes):
    if cls > 3741:
        issue('out_of_range_class', (code, cls))
    if (cls < 3741) != (code in valid):
        issue('raw_coverage', (code, cls, code in valid))
for a, code in enumerate(reps):
    if code not in valid or classes[code] != a:
        issue('representative', (a, code, classes[code], code in valid))
for code, (arrival, rows) in valid.items():
    cls = classes[code] % 3741
    for d, (allowed, k, successor) in enumerate(rows):
        if (dest[cls][d] != 0) != allowed:
            issue('admissibility', (code, cls, d, allowed, dest[cls][d]))
        if allowed:
            if kind[cls][d] != k:
                issue('kind', (code, cls, d, k, kind[cls][d]))
            if (max(dest[cls][d]-1, 0) % 3741) != (classes[successor] % 3741):
                issue('successor', (code, cls, d, successor, dest[cls][d], classes[successor]))
            if k != 2 and reps[cls] % 4 != arrival:
                issue('arrival', (code, cls, d, arrival, reps[cls] % 4))
    # Paper asks same kind even for inadmissible directions in the projection lemma.
    rep_rows = valid[reps[cls]][1]
    for d in range(4):
        if rows[d][1] != rep_rows[d][1]:
            issue('all_direction_kind', (code, cls, d))

edge_counts = Counter()
for a in range(3741):
    for d in range(4):
        if not (dest[a][d] <= 3741 and ((dest[a][d] == 0) == (kind[a][d] == 3))):
            issue('row_encoding', (a, d, dest[a][d], kind[a][d]))
        if dest[a][d] != 0:
            edge_counts[kind[a][d]] += 1

chunk_results = []
for name, offset, width in raw_pieces:
    if name not in {f'rawClass_{i}' for i in range(20, 25)}:
        continue
    lo, hi = offset // 12, (offset+width-1)//12
    relevant = range(lo, hi+1)
    valid_codes = [c for c in relevant if c in valid]
    chunk_results.append({
        'name': name,
        'bit_offset': offset,
        'bit_width': width,
        'codes_touching': [lo, hi],
        'valid_words_touching': len(valid_codes),
        'invalid_words_touching': hi-lo+1-len(valid_codes),
        'classes_of_valid_words': sorted({classes[c] for c in valid_codes}),
        'boundary_codes': {str(c): classes[c] for c in [lo, hi]},
        'coverage_errors': [[c, classes[c], c in valid] for c in relevant if (classes[c] < 3741) != (c in valid)],
    })

result = {
    'counts_by_depth': counts,
    'raw_class_bit_length': raw.bit_length(),
    'raw_class_lanes': len(classes),
    'class_value_counts': {'valid': sum(v < 3741 for v in classes), 'sentinel_3741': classes.count(3741)},
    'issues': dict(issues),
    'first_examples': examples,
    'edge_counts': dict(edge_counts),
    'assigned_chunks': chunk_results,
}
Path('check_results.json').write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps(result, indent=2))
