"""Independent finite audit of the supplied Lean automaton literals.

Reads only the designated Lean input; no archived file is assumed available.
"""
import ast
from collections import Counter
import hashlib
import json
from pathlib import Path
import re

SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
TARGETS = range(515, 520)
text = SOURCE.read_text()
values = {}
hexes = {}
lines = {}
expressions = {}
for line_number, line in enumerate(text.splitlines(), 1):
    match = re.fullmatch(r'(?:private )?noncomputable def (\w+) : ℕ := (.+)', line)
    if not match:
        continue
    name, expr = match.groups()
    lines[name] = line_number
    expressions[name] = expr
    if expr.startswith('0x'):
        hexes[name] = expr[2:]
        values[name] = int(expr, 16)
    else:
        tree = ast.parse(expr.replace('<<<', '<<'), mode='eval')
        def evaluate(node):
            if isinstance(node, ast.Expression):
                return evaluate(node.body)
            if isinstance(node, ast.Name):
                return values[node.id]
            if isinstance(node, ast.Constant) and type(node.value) is int:
                return node.value
            if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add):
                return evaluate(node.left) + evaluate(node.right)
            if isinstance(node, ast.BinOp) and isinstance(node.op, ast.LShift):
                return evaluate(node.left) << evaluate(node.right)
            raise ValueError(ast.dump(node))
        values[name] = evaluate(tree)

def offsets(node, offset=0):
    if isinstance(node, ast.Expression):
        yield from offsets(node.body, offset)
    elif isinstance(node, ast.Name):
        yield node.id, offset
    elif isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add):
        yield from offsets(node.left, offset)
        yield from offsets(node.right, offset)
    elif isinstance(node, ast.BinOp) and isinstance(node.op, ast.LShift):
        assert isinstance(node.right, ast.Constant)
        yield from offsets(node.left, offset + node.right.value)
    else:
        raise ValueError(ast.dump(node))

packed = {name: values[name] for name in ('rawClass', 'representatives', 'destinations', 'edgeKinds')}
raw_offsets = dict(offsets(ast.parse(expressions['rawClass'].replace('<<<', '<<'), mode='eval')))
chunks = [hexes[f'rawClass_{i}'] for i in range(768)]
assert packed['rawClass'] == int(''.join(chunks), 16)
assert sum(len(h) for h in chunks) == 3_145_727
raw_bytes = packed['rawClass'].to_bytes((12 * 4**10 + 7) // 8, 'little')
def raw(code):
    byte = (12 * code) // 8
    shift = (12 * code) % 8
    return ((raw_bytes[byte] | (raw_bytes[byte + 1] << 8)) >> shift) & 4095

def lane(name, width, index):
    return (packed[name] >> (width * index)) & ((1 << width) - 1)

steps = ((1, 0), (0, 1), (-1, 0), (0, -1))
def word(code):
    return tuple((code >> (2 * (9 - i))) & 3 for i in range(10))

def bond(a, b):
    return tuple(sorted((a, b)))

def geometry(code):
    directions = word(code)
    vertices = [(0, 0)]
    bonds = set()
    for d in directions:
        x, y = vertices[-1]
        dx, dy = steps[d]
        z = x + dx, y + dy
        e = bond(vertices[-1], z)
        assert e not in bonds
        bonds.add(e)
        vertices.append(z)
    revisit = vertices[-1] in vertices[:-1]
    result = []
    x, y = vertices[-1]
    for d, (dx, dy) in enumerate(steps):
        allowed = d != ((directions[-1] + 2) % 4) and bond((x, y), (x + dx, y + dy)) not in bonds
        kind = 2 if revisit else (0 if d == directions[-1] else 1)
        successor = ((code & ((1 << 18) - 1)) << 2) + d
        result.append((allowed, kind, successor))
    return directions[-1], result

valid = set()
counts = [1] + [0] * 10
def generate(code, depth, pos, used):
    if depth == 10:
        valid.add(code)
        return
    for d, (dx, dy) in enumerate(steps):
        dest = pos[0] + dx, pos[1] + dy
        e = bond(pos, dest)
        if e not in used:
            counts[depth + 1] += 1
            used.add(e)
            generate(4 * code + d, depth + 1, dest, used)
            used.remove(e)
generate(0, 0, (0, 0), set())

coverage_errors = []
for code in range(4**10):
    a = raw(code)
    if a > 3741 or ((a < 3741) != (code in valid)):
        coverage_errors.append((code, a, code in valid))

representative_errors = []
transition_errors = []
arrivals = {}
rows = {}
edges = Counter()
for a in range(3741):
    code = lane('representatives', 20, a)
    if code not in valid or raw(code) != a:
        representative_errors.append((a, code, raw(code)))
        continue
    arrival, row = geometry(code)
    arrivals[a] = arrival
    rows[a] = row
    for d, (allowed, kind, successor) in enumerate(row):
        dest = lane('destinations', 12, 4 * a + d)
        stored_kind = lane('edgeKinds', 2, 4 * a + d)
        if dest > 3741 or (dest == 0) != (stored_kind == 3) or (dest != 0 and stored_kind >= 3):
            transition_errors.append(('stored_range', a, d, dest, stored_kind))
        if (dest != 0) != allowed or (allowed and (stored_kind != kind or dest - 1 != raw(successor))):
            transition_errors.append(('representative_row', a, code, d, dest, stored_kind, allowed, kind, raw(successor)))
        if allowed:
            edges[kind] += 1

compatibility_errors = []
for code in sorted(valid):
    a = raw(code)
    if a not in rows:
        compatibility_errors.append(('class_missing', code, a))
        continue
    arrival, row = geometry(code)
    for d, ((allowed, kind, successor), (rep_allowed, rep_kind, rep_successor)) in enumerate(zip(row, rows[a])):
        # Correct requires kind/successor equality on admitted edges. The paper
        # also asks for identical kind on all directions; check that too.
        if allowed != rep_allowed or kind != rep_kind or (allowed and raw(successor) != raw(rep_successor)):
            compatibility_errors.append(('row', code, a, d, allowed, kind, raw(successor), rep_allowed, rep_kind, raw(rep_successor)))
        if allowed and kind != 2 and arrival != arrivals[a]:
            compatibility_errors.append(('arrival', code, a, d, arrival, arrivals[a]))

target_summary = []
for i in TARGETS:
    name = f'rawClass_{i}'
    offset = raw_offsets[name]
    length = len(hexes[name]) * 4
    assert ((packed['rawClass'] >> offset) & ((1 << length) - 1)) == values[name]
    affected = range(offset // 12, (offset + length - 1) // 12 + 1)
    actual_valid = [code for code in affected if code in valid]
    errors = [e for e in coverage_errors if e[0] in affected]
    errors += [e for e in compatibility_errors if e[1] in affected]
    target_summary.append({
        'name': name, 'line': lines[name], 'hex_digits': len(hexes[name]),
        'sha256_of_hex_ascii': hashlib.sha256(hexes[name].encode()).hexdigest(),
        'global_bit_offset': offset, 'end_bit_inclusive': offset + length - 1,
        'low_boundary_bit_within_lane': offset % 12,
        'high_boundary_bit_within_lane': (offset + length - 1) % 12,
        'affected_codes_inclusive': [affected.start, affected.stop - 1],
        'affected_lane_count': len(affected), 'valid_codes': len(actual_valid),
        'invalid_codes': len(affected) - len(actual_valid),
        'class_min': min(map(raw, actual_valid)) if actual_valid else None,
        'class_max': max(map(raw, actual_valid)) if actual_valid else None,
        'first_valid': [[code, raw(code), word(code)] for code in actual_valid[:2]],
        'last_valid': [[code, raw(code), word(code)] for code in actual_valid[-2:]],
        'coverage_or_compatibility_error_count': len(errors),
    })

result = {
    'source_sha256': hashlib.sha256(text.encode()).hexdigest(),
    'generated_counts_depth_0_to_10': counts,
    'literal_definition_count': len(hexes), 'raw_chunk_count': len(chunks),
    'all_raw_chunks_below_2pow16384': all(values[f'rawClass_{i}'] < 2**16384 for i in range(768)),
    'raw_table_equals_hex_concatenation': True,
    'coverage_errors_count': len(coverage_errors), 'coverage_errors_first': coverage_errors[:8],
    'representative_errors_count': len(representative_errors), 'representative_errors_first': representative_errors[:8],
    'transition_errors_count': len(transition_errors), 'transition_errors_first': transition_errors[:8],
    'compatibility_errors_count': len(compatibility_errors), 'compatibility_errors_first': compatibility_errors[:8],
    'edge_counts_straight_turn_revisit': [edges[k] for k in range(3)],
    'targets': target_summary,
}
Path('check_results.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
