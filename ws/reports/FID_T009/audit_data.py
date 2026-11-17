"""Read-only reconstruction of the assigned packed automaton data."""
from pathlib import Path
import ast
from collections import Counter
import json
import re

SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
text = SOURCE.read_text()
literals = {name: int(value, 16) for name, value in re.findall(
    r'private noncomputable def (\w+) : ℕ := (0x[0-9a-f]+)', text)}


def flatten(node, offset=0):
    if isinstance(node, ast.Name):
        return [(offset, node.id)]
    assert isinstance(node, ast.BinOp)
    if isinstance(node.op, ast.Add):
        return flatten(node.left, offset) + flatten(node.right, offset)
    assert isinstance(node.op, ast.LShift) and isinstance(node.right, ast.Constant)
    return flatten(node.left, offset + node.right.value)


tables = {}
offsets = {}
packing = {}
for name, width, count in [('rawClass', 12, 4**10), ('representatives', 20, 3741),
                           ('destinations', 12, 3741*4), ('edgeKinds', 2, 3741*4)]:
    expr = re.search(r'^noncomputable def ' + name + r' : ℕ := (.+)$', text, re.M)[1]
    leaves = sorted(flatten(ast.parse(expr.replace('<<<', '<<'), mode='eval').body))
    total = 0
    assert len({key for _, key in leaves}) == len(leaves)
    for i, (offset, key) in enumerate(leaves):
        end = leaves[i+1][0] if i+1 < len(leaves) else width*count
        assert 0 <= literals[key] < 2**(end-offset), (key, offset, end)
        total += literals[key] << offset
        offsets[key] = (offset, end)
    assert len(leaves) == len([key for key in literals if key.startswith(name+'_')])
    tables[name] = (width, count, total.to_bytes((width*count+7)//8, 'little'))
    packing[name] = {'lanes': count, 'width': width, 'chunks': len(leaves),
                     'first_leaf': leaves[0], 'last_leaf': leaves[-1]}


def lane(table, index):
    width, count, data = tables[table]
    assert 0 <= index < count
    bit = width*index
    pos = bit//8
    return (int.from_bytes(data[pos:pos+(width+14)//8], 'little') >> (bit % 8)) & (2**width-1)


def project(code):
    return lane('rawClass', code) % 3741


STEPS = [(1, 0), (0, 1), (-1, 0), (0, -1)]


def decode(code):
    return [(code >> (2*(9-i))) & 3 for i in range(10)]


def word_info(code):
    word = decode(code)
    vertices = [(0, 0)]
    bonds = set()
    raw = True
    for d in word:
        x, y = vertices[-1]
        dx, dy = STEPS[d]
        end = (x+dx, y+dy)
        bond = tuple(sorted((vertices[-1], end)))
        if bond in bonds:
            raw = False
        bonds.add(bond)
        vertices.append(end)
    revisit = vertices[-1] in vertices[:-1]
    admissible = []
    kinds = []
    for d, (dx, dy) in enumerate(STEPS):
        x, y = vertices[-1]
        bond = tuple(sorted(((x, y), (x+dx, y+dy))))
        admissible.append(d != (word[-1]+2) % 4 and bond not in bonds)
        kinds.append(2 if revisit else (0 if d == word[-1] else 1))
    return raw, word[-1], admissible, kinds, vertices


raw_codes = []
counts = Counter()


def generate(code=0, depth=0, endpoint=(0, 0), used=frozenset()):
    counts[depth] += 1
    if depth == 10:
        raw_codes.append(code)
        return
    x, y = endpoint
    for d, (dx, dy) in enumerate(STEPS):
        end = (x+dx, y+dy)
        bond = tuple(sorted((endpoint, end)))
        if bond not in used:
            generate(code*4+d, depth+1, end, used | {bond})


generate()
assert len(raw_codes) == 60092 and raw_codes == sorted(set(raw_codes))
raw_set = set(raw_codes)
reps = [lane('representatives', a) for a in range(3741)]
rep_info = [word_info(c) for c in reps]

coverage_errors = []
for code in range(4**10):
    value = lane('rawClass', code)
    if not (value <= 3741 and ((value < 3741) == (code in raw_set))):
        coverage_errors.append({'code': code, 'value': value, 'raw': code in raw_set})

representative_errors = []
for a, code in enumerate(reps):
    if code >= 4**10 or not rep_info[a][0] or project(code) != a:
        representative_errors.append({'a': a, 'code': code, 'actual_class': project(code)})

row_errors = []
for code in raw_codes:
    raw, arrival, allowed, kinds, vertices = word_info(code)
    assert raw
    a = project(code)
    _, rep_arrival, rep_allowed, rep_kinds, _ = rep_info[a]
    for d in range(4):
        destination = lane('destinations', 4*a+d)
        kind = lane('edgeKinds', 4*a+d)
        failures = []
        if allowed[d] != bool(destination): failures.append('stored_admissibility')
        if allowed[d] != rep_allowed[d]: failures.append('representative_admissibility')
        if kinds[d] != rep_kinds[d]: failures.append('representative_kind')
        if allowed[d]:
            if kind != kinds[d]: failures.append('stored_kind')
            actual = project((code % 4**9)*4+d)
            if (max(destination-1, 0) % 3741) != actual: failures.append('successor')
            if kinds[d] != 2 and arrival != rep_arrival: failures.append('arrival')
        if failures:
            row_errors.append({'code': code, 'a': a, 'd': d, 'failures': failures,
                               'destination': destination, 'kind': kind,
                               'representative': reps[a]})

assigned = {}
for n in range(10, 15):
    key = f'rawClass_{n}'
    start, end = offsets[key]
    lo, hi = start//12, (end-1)//12
    codes = list(range(lo, hi+1))
    assigned[key] = {
        'source_line': 15+2*n, 'bit_range_half_open': [start, end],
        'code_range_inclusive': [lo, hi], 'touched_lanes': len(codes),
        'valid_words': sum(c in raw_set for c in codes),
        'coverage_errors': [e for e in coverage_errors if lo <= e['code'] <= hi],
        'representative_errors': [e for e in representative_errors if lo <= e['code'] <= hi],
        'row_errors': [e for e in row_errors if lo <= e['code'] <= hi],
    }

edge_counts = Counter()
table_row_errors = []
for a in range(3741):
    for d in range(4):
        destination = lane('destinations', 4*a+d)
        kind = lane('edgeKinds', 4*a+d)
        if destination > 3741 or ((destination == 0) != (kind == 3)):
            table_row_errors.append([a, d, destination, kind])
        if destination:
            edge_counts[kind] += 1

result = {'packing': packing, 'raw_counts': dict(sorted(counts.items())),
          'coverage_errors_total': len(coverage_errors),
          'representative_errors_total': len(representative_errors),
          'row_errors_total': len(row_errors), 'edge_counts': dict(edge_counts),
          'table_row_errors_total': len(table_row_errors), 'assigned': assigned,
          'all_coverage_errors': coverage_errors,
          'all_representative_errors': representative_errors,
          'all_row_errors': row_errors}
Path('audit_results.json').write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps(result, indent=2))
