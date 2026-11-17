"""Read-only reconstruction of the Lean literal tables and paper finite checks."""
from pathlib import Path
import ast
from collections import Counter
import json
import re

SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
text = SOURCE.read_text()
literal_matches = list(re.finditer(
    r'^private noncomputable def (\w+) : ℕ := 0x([0-9a-fA-F]+)$', text, re.M))
literals = {m[1]: int(m[2], 16) for m in literal_matches}
hexes = {m[1]: m[2] for m in literal_matches}
lines = {m[1]: text.count('\n', 0, m.start()) + 1 for m in literal_matches}
offsets = {}


def evaluate(node, offset=0):
    if isinstance(node, ast.Name):
        assert node.id not in offsets
        offsets[node.id] = offset
        return literals[node.id]
    assert isinstance(node, ast.BinOp)
    if isinstance(node.op, ast.Add):
        return evaluate(node.left, offset) + evaluate(node.right, offset)
    assert isinstance(node.op, ast.LShift)
    assert isinstance(node.right, ast.Constant) and node.right.value >= 0
    return evaluate(node.left, offset + node.right.value) << node.right.value


tables = {}
assembly = {}
for name in ('rawClass', 'representatives', 'destinations', 'edgeKinds'):
    expr = re.search(r'^noncomputable def ' + name + r' : ℕ := (.+)$', text, re.M)[1]
    tables[name] = evaluate(ast.parse(expr.replace('<<<', '<<'), mode='eval').body)
    names = sorted((k for k in literals if k.startswith(name + '_')),
                   key=lambda k: int(k.rsplit('_', 1)[1]))
    assert tables[name] == int(''.join(hexes[k] for k in names), 16)
    intervals = sorted((offsets[k], offsets[k] + 4 * len(hexes[k]), k) for k in names)
    assert intervals[0][0] == 0
    assert all(a[1] == b[0] for a, b in zip(intervals, intervals[1:]))
    assembly[name] = {'chunks': len(names), 'allocated_bits': intervals[-1][1],
                      'bit_length': tables[name].bit_length(),
                      'concatenation_matches_expression': True}
assert set(offsets) == set(literals)

N = 4**10
raw_bytes = tables['rawClass'].to_bytes(N * 12 // 8, 'little')
raw = []
for i in range(0, len(raw_bytes), 3):
    lane_pair = int.from_bytes(raw_bytes[i:i + 3], 'little')
    raw.extend((lane_pair & 4095, lane_pair >> 12))
assert len(raw) == N


def lanes(name, width, count):
    return [(tables[name] >> (width * i)) & ((1 << width) - 1) for i in range(count)]


representatives = lanes('representatives', 20, 3741)
destinations = lanes('destinations', 12, 4 * 3741)
kinds = lanes('edgeKinds', 2, 4 * 3741)
steps = ((1, 0), (0, 1), (-1, 0), (0, -1))


def bond(p, q):
    return tuple(sorted((p, q)))


def state(code):
    word = tuple((code >> (2 * (9 - i))) & 3 for i in range(10))
    vertices = [(0, 0)]
    bonds = []
    for d in word:
        p = vertices[-1]
        q = (p[0] + steps[d][0], p[1] + steps[d][1])
        vertices.append(q)
        bonds.append(bond(p, q))
    return word, vertices, set(bonds)


errors = []


def require(test, detail):
    if not test:
        errors.append(detail)


for a, code in enumerate(representatives):
    w, vs, bs = state(code)
    require(code < N and len(bs) == 10 and raw[code] == a,
            ('representative', a, code, raw[code]))
for j, (dest, kind) in enumerate(zip(destinations, kinds)):
    require(dest <= 3741 and ((dest == 0) == (kind == 3)), ('row_encoding', j, dest, kind))

raw_codes = set()
depth_counts = [0] * 11
direction_checks = 0
nonrevisit_arrival_checks = 0
class_signatures = {}


def generate(word=(), vertices=((0, 0),), used=frozenset(), code=0):
    global direction_checks, nonrevisit_arrival_checks
    depth_counts[len(word)] += 1
    if len(word) < 10:
        p = vertices[-1]
        for d, (dx, dy) in enumerate(steps):
            q = (p[0] + dx, p[1] + dy)
            e = bond(p, q)
            if e not in used:
                generate(word + (d,), vertices + (q,), used | {e}, code * 4 + d)
        return
    raw_codes.add(code)
    a = raw[code]
    require(a < 3741, ('raw_class_range', code, a))
    if a >= 3741:
        return
    p = vertices[-1]
    revisit = p in vertices[:-1]
    signature = []
    for d, (dx, dy) in enumerate(steps):
        direction_checks += 1
        q = (p[0] + dx, p[1] + dy)
        admissible = d != (word[-1] + 2) % 4 and bond(p, q) not in used
        total_kind = 2 if revisit else 0 if d == word[-1] else 1
        signature.append((admissible, total_kind,
                          raw[(code % (4**9)) * 4 + d] if admissible else None))
        dest = destinations[4 * a + d]
        kind = kinds[4 * a + d]
        require(admissible == (dest != 0), ('admissibility', code, a, d, admissible, dest))
        if admissible:
            expected_kind = 2 if revisit else 0 if d == word[-1] else 1
            require(kind == expected_kind, ('kind', code, a, d, expected_kind, kind))
            successor = (code % (4**9)) * 4 + d
            require(dest - 1 == raw[successor],
                    ('successor', code, a, d, successor, raw[successor], dest - 1))
            if expected_kind != 2:
                nonrevisit_arrival_checks += 1
                require(representatives[a] % 4 == word[-1],
                        ('arrival', code, a, d, word[-1], representatives[a] % 4))
    signature = tuple(signature)
    require(class_signatures.setdefault(a, signature) == signature,
            ('class_signature', code, a))


generate()
for code, a in enumerate(raw):
    require(a <= 3741 and ((a < 3741) == (code in raw_codes)),
            ('raw_coverage', code, a, code in raw_codes))

targets = {}
for i in range(520, 525):
    name = f'rawClass_{i}'
    lo = offsets[name]
    hi = lo + 4 * len(hexes[name]) - 1
    codes = range(lo // 12, hi // 12 + 1)
    raw_in_range = [c for c in codes if c in raw_codes]
    associated_errors = []
    for err in errors:
        if err[0] in ('raw_class_range', 'admissibility', 'kind', 'successor', 'arrival', 'raw_coverage', 'class_signature'):
            if err[1] in codes:
                associated_errors.append(err)
    targets[name] = {
        'line': lines[name], 'hex_digits': len(hexes[name]),
        'bit_length': literals[name].bit_length(), 'low_bit': lo, 'high_bit': hi,
        'first_intersecting_code': codes.start, 'last_intersecting_code': codes.stop - 1,
        'first_code_base4': ''.join(str(d) for d in state(codes.start)[0]),
        'last_code_base4': ''.join(str(d) for d in state(codes.stop - 1)[0]),
        'intersecting_lanes': len(codes), 'raw_lanes': len(raw_in_range),
        'invalid_lanes': len(codes) - len(raw_in_range),
        'class_count': len({raw[c] for c in raw_in_range}),
        'associated_error_count': len(associated_errors),
        'first_associated_errors': associated_errors[:5],
    }

result = {
    'assembly': assembly, 'enumerated_counts_depth_1_to_10': depth_counts[1:],
    'raw_words': len(raw_codes), 'invalid_words': N - len(raw_codes),
    'represented_classes': len(set(raw[c] for c in raw_codes)),
    'direction_checks': direction_checks, 'nonrevisit_arrival_checks': nonrevisit_arrival_checks,
    'class_signatures_including_inadmissible_direction_kinds': len(class_signatures),
    'edge_counts': dict(Counter(k for d, k in zip(destinations, kinds) if d)),
    'error_count': len(errors), 'first_errors': errors[:15], 'targets': targets,
}
print(json.dumps(result, indent=2))
Path('audit_results.json').write_text(json.dumps(result, indent=2) + '\n')
