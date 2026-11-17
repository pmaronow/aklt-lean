from pathlib import Path
import ast
import re
from collections import Counter

SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
s = SOURCE.read_text()
values = {}
expressions = {}
line_numbers = {}
for lineno, line in enumerate(s.splitlines(), 1):
    match = re.fullmatch(r'(?:private )?noncomputable def (\w+) : ℕ := (.*)', line)
    if not match:
        continue
    name, expression = match.groups()
    line_numbers[name] = lineno
    if expression.startswith('0x'):
        values[name] = int(expression, 16)
    else:
        expressions[name] = ast.parse(expression.replace('<<<', '<<'), mode='eval').body

def evaluate(node):
    if isinstance(node, ast.Name):
        return values[node.id]
    if isinstance(node, ast.Constant):
        return node.value
    if isinstance(node, ast.BinOp):
        left, right = evaluate(node.left), evaluate(node.right)
        if isinstance(node.op, ast.Add):
            return left + right
        if isinstance(node.op, ast.LShift):
            return left << right
    raise ValueError(ast.dump(node))

def offsets(node, offset=0):
    if isinstance(node, ast.Name):
        return {node.id: offset}
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add):
        a, b = offsets(node.left, offset), offsets(node.right, offset)
        assert not (a.keys() & b.keys())
        return a | b
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.LShift):
        return offsets(node.left, offset + evaluate(node.right))
    raise ValueError(ast.dump(node))

for name, expression in expressions.items():
    values[name] = evaluate(expression)
    positions = offsets(expression)
    intervals = sorted((o, o + values[n].bit_length(), n) for n, o in positions.items())
    assert all(hi <= nxt for (_, hi, _), (nxt, _, _) in zip(intervals, intervals[1:])), name
    print(f'{name}: {len(positions)} pieces, {values[name].bit_length()} bits, nonoverlapping assembly')

raw = values['rawClass']
# All denominators in Lean lane are positive powers of two. Convert exact
# quotient/remainder into shifts/masks on nonnegative integers.
raw_bytes = raw.to_bytes((raw.bit_length() + 7) // 8, 'little')
def raw_at(code):
    bit = 12 * code
    byte, shift = divmod(bit, 8)
    return (int.from_bytes(raw_bytes[byte:byte+3], 'little') >> shift) & 4095

def lane(packed, width, index):
    return (packed >> (width * index)) & ((1 << width) - 1)

positions = offsets(expressions['rawClass'])
ranges = {}
for i in range(200, 205):
    name = f'rawClass_{i}'
    lo = positions[name]
    hi = lo + 16384
    ranges[name] = range(lo // 12, (hi - 1) // 12 + 1)
    print(name, 'source line', line_numbers[name], 'bit interval', (lo, hi),
          'code range', (ranges[name].start, ranges[name].stop-1),
          'boundary alignment', (lo % 12, hi % 12))
    print('  first/last entries:', [(c, raw_at(c)) for c in list(ranges[name])[:2]+list(ranges[name])[-2:]])

steps = ((1, 0), (0, 1), (-1, 0), (0, -1))
def word(code, length=10):
    return tuple((code >> (2*(length-1-i))) & 3 for i in range(length))

def geometry(w):
    vertices = [(0, 0)]
    bonds = set()
    valid = True
    for d in w:
        x, y = vertices[-1]
        dx, dy = steps[d]
        z = (x+dx, y+dy)
        b = tuple(sorted((vertices[-1], z)))
        if b in bonds:
            valid = False
        bonds.add(b)
        vertices.append(z)
    return vertices, bonds, valid

def row(code):
    w = word(code)
    vertices, bonds, valid = geometry(w)
    assert valid
    endpoint = vertices[-1]
    revisit = endpoint in vertices[:-1]
    out = []
    for d, (dx, dy) in enumerate(steps):
        z = (endpoint[0]+dx, endpoint[1]+dy)
        bond = tuple(sorted((endpoint, z)))
        allowed = d != (w[-1]+2) % 4 and bond not in bonds
        kind = 2 if revisit else (0 if d == w[-1] else 1)
        succ = ((code & ((1 << 18)-1)) << 2) | d
        out.append((allowed, kind, raw_at(succ)))
    return out, w[-1]

# Independently generate exactly the words with distinct unoriented bonds.
valid_codes = set()
counts = Counter()
def generate(code=0, depth=0, endpoint=(0, 0), bonds=None):
    if bonds is None:
        bonds = set()
    counts[depth] += 1
    if depth == 10:
        valid_codes.add(code)
        return
    for d, (dx, dy) in enumerate(steps):
        z = (endpoint[0]+dx, endpoint[1]+dy)
        bond = tuple(sorted((endpoint, z)))
        if bond in bonds:
            continue
        bonds.add(bond)
        generate(4*code+d, depth+1, z, bonds)
        bonds.remove(bond)
generate()
print('Independent raw counts:', [counts[d] for d in range(1, 11)])

coverage_errors = []
for code in range(4**10):
    a = raw_at(code)
    if a > 3741 or ((a < 3741) != (code in valid_codes)):
        coverage_errors.append((code, a, code in valid_codes))
print('Global coverage errors:', len(coverage_errors), coverage_errors[:20])

reps = [lane(values['representatives'], 20, a) for a in range(3741)]
rep_errors = [(a, c, raw_at(c), c in valid_codes) for a, c in enumerate(reps)
              if c >= 4**10 or c not in valid_codes or raw_at(c) != a]
print('Representative errors:', len(rep_errors), rep_errors[:20])
rep_rows = [row(c) for c in reps]

def errors(code):
    a = raw_at(code)
    if a >= 3741:
        return [('class_out_of_range', a)]
    actual, arrival = row(code)
    expected, rep_arrival = rep_rows[a]
    problems = []
    for d, ((ok, kind, succ), (rep_ok, rep_kind, rep_succ)) in enumerate(zip(actual, expected)):
        if ok != rep_ok:
            problems.append(('admissibility', d, ok, rep_ok))
        # Paper compares kind with the representative for all directions.
        if kind != rep_kind:
            problems.append(('kind', d, kind, rep_kind))
        if ok and succ != rep_succ:
            problems.append(('successor', d, succ, rep_succ))
        if ok and kind != 2 and arrival != rep_arrival:
            problems.append(('arrival', d, arrival, rep_arrival))
    return problems

for name, codes in ranges.items():
    valid = [code for code in codes if code in valid_codes]
    bad_coverage = [e for e in coverage_errors if e[0] in codes]
    bad_rows = [(c, raw_at(c), errors(c)) for c in valid if errors(c)]
    print(name, 'valid words', len(valid), 'invalid words', len(codes)-len(valid),
          'coverage errors', bad_coverage, 'quotient errors', bad_rows[:10], 'total', len(bad_rows))

global_quotient_errors = [(c, raw_at(c), problems) for c in sorted(valid_codes)
                          if (problems := errors(c))]
print('All-raw-word quotient errors:', len(global_quotient_errors), global_quotient_errors[:20])

# Stored class rows themselves are independently compared with representatives.
row_errors = []
edge_counts = Counter()
for a, (expected, _) in enumerate(rep_rows):
    for d, (ok, kind, succ) in enumerate(expected):
        dest = lane(values['destinations'], 12, 4*a+d)
        k = lane(values['edgeKinds'], 2, 4*a+d)
        if dest != (succ+1 if ok else 0) or k != (kind if ok else 3):
            row_errors.append((a, d, dest, k, ok, kind, succ))
        if ok:
            edge_counts[kind] += 1
print('Stored class row errors:', len(row_errors), row_errors[:20])
print('Regenerated labelled edge counts:', dict(sorted(edge_counts.items())))
assert not coverage_errors
assert not rep_errors
assert not global_quotient_errors
assert not row_errors
assert edge_counts == Counter({0: 2516, 1: 5032, 2: 1872})
assert [counts[d] for d in range(1, 11)] == [4, 12, 36, 108, 316, 916, 2628, 7500, 21268, 60092]

# Exact witness details for coverage mismatches involving assigned chunks.
for code, a, valid in coverage_errors:
    containing = [n for n, codes in ranges.items() if code in codes]
    if containing:
        print('WITNESS:', code, 'hex', hex(code), 'directions', word(code),
              'class', a, 'valid', valid, 'chunks', containing)
        print('  vertices, bonds, valid:', geometry(word(code)))
        print('  bit positions of lane:', (12*code, 12*code+12))
        for n in containing:
            print(' ', n, 'low offset', positions[n], 'low 16 bits', hex(values[n] & 65535))
