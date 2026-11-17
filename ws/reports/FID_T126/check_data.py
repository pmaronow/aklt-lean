"""Independent finite audit of the supplied Lean literals; reads only permitted inputs."""
from pathlib import Path
import ast
from array import array
from collections import Counter
import hashlib
import json
import re

ROOT = Path('/home/ubuntu/aklt/review/FID_T/lean')
SOURCE = ROOT / 'AKLT/Defs/Automaton10Data.lean'
source = SOURCE.read_text()
values = {}
lines = {}
expressions = {}
for lineno, line in enumerate(source.splitlines(), 1):
    match = re.fullmatch(r'(?:private )?noncomputable def (\w+) : ℕ := (.+)', line)
    if match:
        name, expression = match.groups()
        lines[name] = lineno
        expressions[name] = expression
        if expression.startswith('0x'):
            assert re.fullmatch(r'0x[0-9a-f]+', expression)
            values[name] = int(expression, 16)

# All binary operators in these four expressions are explicitly parenthesized.
# Evaluate only names, natural numerals, addition and natural left shift.
positions = {}
def evaluate(node):
    if isinstance(node, ast.Name):
        return values[node.id], {node.id: 0}
    if isinstance(node, ast.Constant):
        assert isinstance(node.value, int) and node.value >= 0
        return node.value, {}
    assert isinstance(node, ast.BinOp)
    left, lp = evaluate(node.left)
    right, rp = evaluate(node.right)
    if isinstance(node.op, ast.Add):
        assert not (lp.keys() & rp.keys())
        return left + right, lp | rp
    assert isinstance(node.op, ast.LShift) and not rp
    return left << right, {name: offset + right for name, offset in lp.items()}

for name in ('rawClass', 'representatives', 'destinations', 'edgeKinds'):
    expression = expressions[name].replace('<<<', '<<')
    values[name], positions[name] = evaluate(ast.parse(expression, mode='eval').body)

assert len(positions['rawClass']) == 768
assert positions['rawClass']['rawClass_767'] == 0
for i in range(768):
    n = f'rawClass_{i}'
    expected_offset = (767 - i) * 16384 - 4 if i < 767 else 0
    # The final chunk occupies 16380 bits: total table is 12*4^10 bits.
    assert positions['rawClass'][n] == expected_offset
    width = 16380 if i == 767 else 16384
    assert 0 <= values[n] < 2**width
assert values['rawClass'].bit_length() <= 12 * 4**10

packed_bytes = {name: value.to_bytes((value.bit_length()+7)//8, 'little')
                for name, value in values.items() if name in positions}
def lane(name, width, index):
    offset = width * index
    first = offset // 8
    last = (offset + width + 7) // 8
    return (int.from_bytes(packed_bytes[name][first:last], 'little') >> (offset % 8)) & ((1 << width) - 1)

classes = array('H', (lane('rawClass', 12, code) for code in range(4**10)))
representatives = [lane('representatives', 20, a) for a in range(3741)]
destinations = [[lane('destinations', 12, a*4+d) for d in range(4)] for a in range(3741)]
kinds = [[lane('edgeKinds', 2, a*4+d) for d in range(4)] for a in range(3741)]
STEPS = [(1, 0), (0, 1), (-1, 0), (0, -1)]
def next_point(point, direction):
    dx, dy = STEPS[direction]
    return point[0] + dx, point[1] + dy

def bond(a, b):
    return tuple(sorted((a, b)))

def decode(code):
    return [(code >> (2 * (9-i))) & 3 for i in range(10)]

def geometry(word):
    vertices = [(0, 0)]
    bonds = set()
    raw = True
    for direction in word:
        new = next_point(vertices[-1], direction)
        edge = bond(vertices[-1], new)
        if edge in bonds:
            raw = False
        bonds.add(edge)
        vertices.append(new)
    return raw, vertices, bonds

def row(word, vertices, bonds):
    end = vertices[-1]
    revisited = end in vertices[:-1]
    allowed = [d != ((word[-1]+2)%4) and bond(end, next_point(end, d)) not in bonds for d in range(4)]
    kind = [2 if revisited else (0 if d == word[-1] else 1) for d in range(4)]
    return allowed, kind

raw = {}
counts_by_length = Counter()
def generate(word, vertices, used, code):
    counts_by_length[len(word)] += 1
    if len(word) == 10:
        raw[code] = (word, vertices, used)
        return
    end = vertices[-1]
    for d in range(4):
        new = next_point(end, d)
        edge = bond(end, new)
        if edge not in used:
            generate(word+[d], vertices+[new], used | {edge}, code*4+d)
generate([], [(0,0)], set(), 0)

errors = []
def check(condition, error):
    if not condition:
        errors.append(error)

for code, a in enumerate(classes):
    check(a <= 3741, ('range', code, a))
    check((a < 3741) == (code in raw), ('coverage', code, a, code in raw))

rep_geometry = []
for a, code in enumerate(representatives):
    check(code < 4**10, ('representative bound', a, code))
    word = decode(code)
    valid, vertices, bonds = geometry(word)
    check(valid, ('representative not raw', a, code))
    check(classes[code] == a, ('representative class', a, code, classes[code]))
    rep_geometry.append((word, row(word, vertices, bonds)))
    for d in range(4):
        dest, kind = destinations[a][d], kinds[a][d]
        check(dest <= 3741, ('destination bound', a, d, dest))
        check((dest == 0) == (kind == 3), ('inadmissible marker', a, d, dest, kind))
        check(dest == 0 or kind < 3, ('kind bound', a, d, kind))

for code, (word, vertices, bonds) in raw.items():
    a = classes[code] % 3741
    allowed, kind = row(word, vertices, bonds)
    repword, (rep_allowed, rep_kind) = rep_geometry[a]
    for d in range(4):
        check(allowed[d] == (destinations[a][d] != 0), ('allowed', code, a, d))
        check(allowed[d] == rep_allowed[d], ('representative allowed', code, a, d))
        check(kind[d] == rep_kind[d], ('representative kind including disallowed', code, a, d))
        if allowed[d]:
            check(kinds[a][d] == kind[d], ('kind', code, a, d, kinds[a][d], kind[d]))
            successor_code = (code % (4**9))*4 + d
            check(successor_code in raw, ('successor not raw', code, d, successor_code))
            check((destinations[a][d]-1) % 3741 == classes[successor_code] % 3741,
                  ('successor', code, a, d, successor_code))
            if kind[d] != 2:
                check(word[-1] == repword[-1], ('arrival', code, a, d))

edge_counts = Counter(kinds[a][d] for a in range(3741) for d in range(4) if destinations[a][d] != 0)
result = {
    'source': str(SOURCE),
    'chunk_count': len(positions['rawClass']),
    'raw_counts': dict(sorted(counts_by_length.items())),
    'class_lane_counts': {'valid': sum(a<3741 for a in classes), 'sentinel': classes.count(3741)},
    'class_range': [min(classes), max(classes)],
    'distinct_valid_classes': len({a for a in classes if a<3741}),
    'representatives': len(representatives),
    'labelled_edge_counts': dict(sorted(edge_counts.items())),
    'error_count': len(errors),
    'first_errors': errors[:20],
    'targets': []
}
for i in range(595,600):
    name = f'rawClass_{i}'
    offset = positions['rawClass'][name]
    end = offset + 16384 - 1
    lo, hi = offset//12, end//12
    touched = range(lo, hi+1)
    valid_codes = [code for code in touched if code in raw]
    result['targets'].append({
        'name': name, 'line': lines[name], 'bits': [offset, end],
        'code_interval': [lo,hi], 'offset_mod_12': offset%12,
        'touched_lane_count': hi-lo+1, 'raw_windows_touched': len(valid_codes),
        'invalid_words_touched': hi-lo+1-len(valid_codes),
        'first_valid_examples': [{'code': c, 'word': ''.join('ENWS'[d] for d in raw[c][0]), 'class': classes[c]} for c in valid_codes[:5]],
        'literal_bit_length': values[name].bit_length(),
        'literal_sha256': hashlib.sha256(expressions[name].encode()).hexdigest(),
    })
print(json.dumps(result, indent=2))
Path('/home/ubuntu/aklt/reports/FID_T126/check_results.json').write_text(json.dumps(result, indent=2)+'\n')
