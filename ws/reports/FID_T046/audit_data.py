"""Independent finite audit using only the supplied Lean source and paper conventions."""

import ast
from collections import Counter
import hashlib
import json
from pathlib import Path
import re

SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
text = SOURCE.read_text()
literals = {}
literal_lines = {}
for line_number, line in enumerate(text.splitlines(), 1):
    match = re.fullmatch(r'private noncomputable def (\w+) : ℕ := 0x([0-9a-fA-F]+)', line)
    if match:
        literals[match[1]] = match[2]
        literal_lines[match[1]] = line_number


def terms(node, shift=0):
    if isinstance(node, ast.Name):
        return [(node.id, shift)]
    assert isinstance(node, ast.BinOp)
    if isinstance(node.op, ast.Add):
        return terms(node.left, shift) + terms(node.right, shift)
    assert isinstance(node.op, ast.LShift)
    assert isinstance(node.right, ast.Constant) and isinstance(node.right.value, int)
    return terms(node.left, shift + node.right.value)


packed = {}
offsets = {}
for table in ('rawClass', 'representatives', 'destinations', 'edgeKinds'):
    expression = re.search(r'^noncomputable def ' + table + r' : ℕ := (.+)$', text, re.M)[1]
    tree = ast.parse(expression.replace('<<<', '<<'), mode='eval').body
    table_terms = terms(tree)
    assert len(table_terms) == len(set(name for name, _ in table_terms))
    accumulated_width = 0
    for name, shift in reversed(table_terms):
        assert shift == accumulated_width, (table, name, shift, accumulated_width)
        offsets[name] = shift
        accumulated_width += 4 * len(literals[name])
    value = sum(int(literals[name], 16) << shift for name, shift in table_terms)
    assert value == int(''.join(literals[name] for name, _ in table_terms), 16)
    packed[table] = value.to_bytes((accumulated_width + 7) // 8, 'little')


def lane(table, width, index):
    bit = width * index
    start, local = divmod(bit, 8)
    end = (bit + width + 7) // 8
    return (int.from_bytes(packed[table][start:end], 'little') >> local) & ((1 << width) - 1)


raw_classes = [lane('rawClass', 12, code) for code in range(4**10)]
representatives = [lane('representatives', 20, a) for a in range(3741)]
destinations = [[lane('destinations', 12, 4*a+d) for d in range(4)] for a in range(3741)]
kinds = [[lane('edgeKinds', 2, 4*a+d) for d in range(4)] for a in range(3741)]

steps = ((1, 0), (0, 1), (-1, 0), (0, -1))
depth_counts = Counter()
raw_codes = set()
class_full_kinds = {}
class_arrivals = {}
errors = []
edge_checks = 0


def bond(x, y):
    return (x, y) if x < y else (y, x)


def walk(code=0, vertex=(0, 0), used=None, vertices=None, depth=0):
    global edge_checks
    if used is None:
        used = set()
        vertices = []
    depth_counts[depth] += 1
    if depth == 10:
        raw_codes.add(code)
        a = raw_classes[code]
        if not 0 <= a < 3741:
            errors.append(('raw class out of range', code, a))
            return
        arrival = code % 4
        revisit = vertex in vertices
        full_kinds = tuple(2 if revisit else 0 if d == arrival else 1 for d in range(4))
        previous = class_full_kinds.setdefault(a, full_kinds)
        if previous != full_kinds:
            errors.append(('kind compatibility including inadmissible directions', code, a))
        for d, (dx, dy) in enumerate(steps):
            new_vertex = (vertex[0] + dx, vertex[1] + dy)
            allowed = d != (arrival + 2) % 4 and bond(vertex, new_vertex) not in used
            if allowed != (destinations[a][d] != 0):
                errors.append(('admissibility', code, a, d))
            if allowed:
                edge_checks += 1
                if kinds[a][d] != full_kinds[d]:
                    errors.append(('kind', code, a, d))
                successor_code = (code % (4**9))*4 + d
                if raw_classes[successor_code] != destinations[a][d] - 1:
                    errors.append(('successor', code, a, d, successor_code))
                if not revisit:
                    if representatives[a] % 4 != arrival:
                        errors.append(('representative arrival', code, a, d))
                    previous_arrival = class_arrivals.setdefault(a, arrival)
                    if previous_arrival != arrival:
                        errors.append(('class arrival', code, a, d))
        return
    vertices.append(vertex)
    for d, (dx, dy) in enumerate(steps):
        new_vertex = (vertex[0] + dx, vertex[1] + dy)
        edge = bond(vertex, new_vertex)
        if edge not in used:
            used.add(edge)
            walk(4*code+d, new_vertex, used, vertices, depth+1)
            used.remove(edge)
    vertices.pop()


walk()
for code, a in enumerate(raw_classes):
    if not (a <= 3741 and ((a < 3741) == (code in raw_codes))):
        errors.append(('coverage', code, a))
for a, code in enumerate(representatives):
    if not (code < 4**10 and code in raw_codes and raw_classes[code] == a):
        errors.append(('representative', a, code))
for a in range(3741):
    for d in range(4):
        dest, kind = destinations[a][d], kinds[a][d]
        if not (dest <= 3741 and ((dest == 0) == (kind == 3)) and (dest == 0 or kind < 3)):
            errors.append(('stored lane range', a, d, dest, kind))

edge_counts = Counter(kinds[a][d] for a in range(3741) for d in range(4) if destinations[a][d] != 0)
assert [depth_counts[j] for j in range(1, 11)] == [4,12,36,108,316,916,2628,7500,21268,60092]
assert edge_counts == Counter({0:2516,1:5032,2:1872})

chunks = []
for i in range(195, 200):
    name = f'rawClass_{i}'
    low = offsets[name]
    high = low + 4*len(literals[name]) - 1
    code_low, code_high = low//12, high//12
    touched = range(code_low, code_high+1)
    valid = [code for code in touched if code in raw_codes]
    chunks.append({
        'declaration': name,
        'lean_line': literal_lines[name],
        'hex_digits': len(literals[name]),
        'bit_range_inclusive': [low, high],
        'code_range_inclusive': [code_low, code_high],
        'code_range_hex': [hex(code_low), hex(code_high)],
        'raw_windows_touched': len(valid),
        'invalid_words_touched': len(touched)-len(valid),
        'raw_classes_touched': len({raw_classes[code] for code in valid}),
        'boundary_lane_values': [raw_classes[code_low], raw_classes[code_high]],
        'literal_hex_sha256': hashlib.sha256(literals[name].encode()).hexdigest(),
    })

result = {
    'raw_window_counts_by_depth': dict(sorted(depth_counts.items())),
    'all_word_codes_checked': len(raw_classes),
    'valid_class_range': [min(raw_classes[c] for c in raw_codes), max(raw_classes[c] for c in raw_codes)],
    'invalid_sentinel_counts': dict(Counter(raw_classes[c] for c in range(4**10) if c not in raw_codes)),
    'representatives_checked': len(representatives),
    'classes_covered': len(class_full_kinds),
    'raw_admissible_edges_checked': edge_checks,
    'quotient_edge_counts': dict(edge_counts),
    'errors_count': len(errors),
    'errors_first_20': errors[:20],
    'chunks': chunks,
}
Path('audit_results.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
assert not errors
