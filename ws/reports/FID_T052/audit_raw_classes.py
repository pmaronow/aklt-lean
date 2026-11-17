"""Read-only independent audit of the supplied packed memory-ten quotient."""
from pathlib import Path
import ast
from collections import Counter
import hashlib
import json
import re

SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
source = SOURCE.read_text()
literals = {}
lines = {}
expressions = {}
for line_no, line in enumerate(source.splitlines(), 1):
    match = re.fullmatch(r'private noncomputable def (\w+) : ℕ := 0x([0-9a-f]+)', line)
    if match:
        name, digits = match.groups()
        literals[name] = int(digits, 16)
        lines[name] = (line_no, digits)
    match = re.fullmatch(r'noncomputable def (\w+) : ℕ := (.*)', line)
    if match:
        expressions[match[1]] = ast.parse(match[2].replace('<<<', '<<'), mode='eval').body


def evaluate(node):
    if isinstance(node, ast.Name):
        return literals[node.id]
    assert isinstance(node, ast.BinOp)
    if isinstance(node.op, ast.Add):
        return evaluate(node.left) + evaluate(node.right)
    assert isinstance(node.op, ast.LShift) and isinstance(node.right, ast.Constant)
    return evaluate(node.left) << node.right.value


def offsets(node, shift=0):
    if isinstance(node, ast.Name):
        return [(node.id, shift)]
    if isinstance(node.op, ast.Add):
        return offsets(node.left, shift) + offsets(node.right, shift)
    assert isinstance(node.op, ast.LShift) and isinstance(node.right, ast.Constant)
    return offsets(node.left, shift + node.right.value)


packed = {name: evaluate(expr) for name, expr in expressions.items()}
for name, expr in expressions.items():
    parts = sorted(offsets(expr), key=lambda item: item[1])
    assert len(parts) == len(set(n for n, _ in parts))
    for (left, lo), (_, hi) in zip(parts, parts[1:]):
        assert literals[left].bit_length() <= hi - lo, (name, left, 'overlap')

blobs = {name: value.to_bytes((value.bit_length() + 7) // 8, 'little')
         for name, value in packed.items()}


def lane(name, width, index):
    bit = width * index
    start, extra = divmod(bit, 8)
    value = int.from_bytes(blobs[name][start:start + (extra + width + 7) // 8], 'little')
    return (value >> extra) & ((1 << width) - 1)


def project(code):
    return lane('rawClass', 12, code)


def decode(code):
    return tuple((code // (4 ** (9-i))) % 4 for i in range(10))


def word_string(code):
    return ''.join('ENWS'[d] for d in decode(code))


STEPS = ((1, 0), (0, 1), (-1, 0), (0, -1))


def geometry(code):
    word = decode(code)
    vertex = (0, 0)
    departed = set()
    bonds = set()
    for d in word:
        dx, dy = STEPS[d]
        nxt = (vertex[0] + dx, vertex[1] + dy)
        bond = frozenset((vertex, nxt))
        if bond in bonds:
            return None
        bonds.add(bond)
        departed.add(vertex)
        vertex = nxt
    admissible = []
    kinds = []
    for d, (dx, dy) in enumerate(STEPS):
        nxt = (vertex[0] + dx, vertex[1] + dy)
        admissible.append(d != (word[-1] + 2) % 4 and frozenset((vertex, nxt)) not in bonds)
        kinds.append(2 if vertex in departed else 0 if d == word[-1] else 1)
    return word[-1], admissible, kinds


# Generate Omega_10 without consulting any table, as in the paper's recursion.
raw_codes = set()
counts = Counter()


def generate(depth, code, vertex, bonds):
    counts[depth] += 1
    if depth == 10:
        raw_codes.add(code)
        return
    for d, (dx, dy) in enumerate(STEPS):
        nxt = (vertex[0] + dx, vertex[1] + dy)
        bond = frozenset((vertex, nxt))
        if bond not in bonds:
            generate(depth + 1, 4 * code + d, nxt, bonds | {bond})


generate(0, 0, (0, 0), set())
assert [counts[i] for i in range(1, 11)] == [4, 12, 36, 108, 316, 916, 2628, 7500, 21268, 60092]
coverage_errors = []
for code in range(4**10):
    value = project(code)
    if not (value <= 3741 and ((value < 3741) == (code in raw_codes))):
        coverage_errors.append((code, value))
assert not coverage_errors, coverage_errors[:10]

representatives = [lane('representatives', 20, a) for a in range(3741)]
for a, code in enumerate(representatives):
    assert code < 4**10 and code in raw_codes and project(code) == a, (a, code)
rep_geometry = [geometry(code) for code in representatives]
destinations = [[lane('destinations', 12, 4*a+d) for d in range(4)] for a in range(3741)]
kinds = [[lane('edgeKinds', 2, 4*a+d) for d in range(4)] for a in range(3741)]
edge_counts = Counter()
for a in range(3741):
    for d in range(4):
        dest, kind = destinations[a][d], kinds[a][d]
        assert dest <= 3741 and ((dest == 0) == (kind == 3))
        if dest:
            assert kind < 3
            edge_counts[kind] += 1
assert [edge_counts[i] for i in range(3)] == [2516, 5032, 1872]

# Check every raw row, including its comparison with its representative.
for code in sorted(raw_codes):
    a = project(code)
    arrival, allowed, kind = geometry(code)
    rep_arrival, rep_allowed, rep_kind = rep_geometry[a]
    assert allowed == rep_allowed and kind == rep_kind, (code, a, 'representative')
    for d in range(4):
        assert bool(destinations[a][d]) == allowed[d], (code, a, d, 'allowed')
        if allowed[d]:
            successor = (code % (4**9)) * 4 + d
            assert successor in raw_codes
            assert kinds[a][d] == kind[d], (code, a, d, 'kind')
            assert destinations[a][d] - 1 == project(successor), (code, a, d, 'successor')
            if kind[d] != 2:
                assert arrival == rep_arrival, (code, a, d, 'arrival')

result = {
    'source_sha256': hashlib.sha256(source.encode()).hexdigest(),
    'literal_counts': dict(Counter(name.rsplit('_', 1)[0] for name in literals)),
    'all_packed_fields_nonoverlapping': True,
    'generated_raw_counts': {i: counts[i] for i in range(1, 11)},
    'full_coverage_errors': len(coverage_errors),
    'representatives_checked': 3741,
    'raw_rows_checked': len(raw_codes),
    'directions_checked': 4 * len(raw_codes),
    'quotient_edge_counts': {i: edge_counts[i] for i in range(3)},
    'targets': {},
}
raw_offsets = dict(offsets(expressions['rawClass']))
for i in range(225, 230):
    name = f'rawClass_{i}'
    line_no, digits = lines[name]
    offset = raw_offsets[name]
    width = len(digits)*4
    first, last = offset // 12, (offset + width - 1) // 12
    classes = Counter(project(code) for code in range(first, last+1))
    valid = [code for code in range(first, last+1) if code in raw_codes]
    examples = []
    for code in valid[:3]:
        a = project(code)
        examples.append({'code': code, 'word': word_string(code), 'class': a,
                         'representative': word_string(representatives[a])})
    result['targets'][name] = {
        'line': line_no, 'hex_digits': len(digits),
        'literal_hex_sha256': hashlib.sha256(digits.encode()).hexdigest(),
        'bit_interval_inclusive': [offset, offset+width-1],
        'intersected_code_interval_inclusive': [first, last],
        'valid_raw_words': len(valid), 'invalid_raw_words': classes[3741],
        'class_values_on_valid_words': sorted({project(code) for code in valid}),
        'examples': examples,
    }

out = Path('/home/ubuntu/aklt/reports/FID_T052/audit_results.json')
out.write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
