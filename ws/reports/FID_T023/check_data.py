"""Independent reconstruction of the supplied Lean literals and trail checks."""
from pathlib import Path
from array import array
from collections import Counter
import ast
import hashlib
import json
import re

SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
text = SOURCE.read_text()
literals = {
    name: int(digits, 16)
    for name, digits in re.findall(
        r'private noncomputable def (\w+) : ℕ := 0x([0-9a-f]+)', text)
}


def unpack_expression(name):
    expression = re.search(r'^noncomputable def ' + name + r' : ℕ := (.+)$', text, re.M)[1]
    tree = ast.parse(expression.replace('<<<', '<<'), mode='eval').body

    def value(node):
        if isinstance(node, ast.Name):
            return literals[node.id]
        if isinstance(node, ast.Constant):
            return node.value
        assert isinstance(node, ast.BinOp)
        if isinstance(node.op, ast.Add):
            return value(node.left) + value(node.right)
        assert isinstance(node.op, ast.LShift)
        return value(node.left) << value(node.right)

    offsets = {}

    def collect(node, offset=0):
        if isinstance(node, ast.Name):
            assert node.id not in offsets
            offsets[node.id] = offset
        elif isinstance(node.op, ast.Add):
            collect(node.left, offset)
            collect(node.right, offset)
        else:
            assert isinstance(node.op, ast.LShift)
            collect(node.left, offset + value(node.right))

    collect(tree)
    ordered = sorted(offsets.items(), key=lambda item: item[1])
    for (lo_name, lo), (_, hi) in zip(ordered, ordered[1:]):
        assert literals[lo_name].bit_length() <= hi - lo, (lo_name, lo, hi)
    return value(tree), offsets


packed = {}
offsets = {}
for name in ('rawClass', 'representatives', 'destinations', 'edgeKinds'):
    packed[name], offsets[name] = unpack_expression(name)


def lanes(name, width, count):
    data = packed[name].to_bytes((width * count + 7) // 8, 'little')
    if width == 12:
        result = array('H')
        for i in range(0, len(data), 3):
            word = int.from_bytes(data[i:i+3], 'little')
            result.extend((word & 4095, (word >> 12) & 4095))
        return result[:count]
    # This loop uses small byte slices, avoiding repeated large-integer shifts.
    result = []
    for i in range(count):
        bit = i * width
        start = bit // 8
        word = int.from_bytes(data[start:(bit+width+7)//8], 'little')
        result.append((word >> (bit % 8)) & ((1 << width)-1))
    return result


classes = lanes('rawClass', 12, 4**10)
reps = lanes('representatives', 20, 3741)
dests = lanes('destinations', 12, 3741*4)
kinds = lanes('edgeKinds', 2, 3741*4)
steps = ((1, 0), (0, 1), (-1, 0), (0, -1))


def path(code):
    directions = [(code >> (2*(9-i))) & 3 for i in range(10)]
    vertices = [(0, 0)]
    bonds = []
    for d in directions:
        x, y = vertices[-1]
        dx, dy = steps[d]
        end = (x+dx, y+dy)
        bonds.append(tuple(sorted((vertices[-1], end))))
        vertices.append(end)
    return directions, vertices, bonds


def row(code):
    directions, vertices, bonds = path(code)
    assert len(set(bonds)) == 10
    current = vertices[-1]
    revisit = current in vertices[:-1]
    output = []
    for d, (dx, dy) in enumerate(steps):
        new = (current[0]+dx, current[1]+dy)
        allowed = d != (directions[-1]+2) % 4 and tuple(sorted((current, new))) not in bonds
        kind = 2 if revisit else (0 if d == directions[-1] else 1)
        successor = ((code % 4**9)*4+d)
        output.append((allowed, kind, successor, directions[-1]))
    return output


valid = set()
depth_counts = [0]*11


def generate(depth, code, current, bonds):
    depth_counts[depth] += 1
    if depth == 10:
        valid.add(code)
        return
    for d, (dx, dy) in enumerate(steps):
        new = (current[0]+dx, current[1]+dy)
        bond = tuple(sorted((current, new)))
        if bond not in bonds:
            bonds.add(bond)
            generate(depth+1, code*4+d, new, bonds)
            bonds.remove(bond)


generate(0, 0, (0, 0), set())
coverage_errors = [i for i, a in enumerate(classes) if
                   (a >= 3741 if i in valid else a != 3741)]
representative_errors = []
for a, code in enumerate(reps):
    if code >= 4**10 or code not in valid or classes[code] != a:
        representative_errors.append((a, code, classes[code]))

row_errors = []
errors_by_code = Counter()
all_direction_kind_errors = []
rep_rows = [row(code) for code in reps]
for code in sorted(valid):
    a = classes[code]
    if a >= 3741:
        row_errors.append((code, 'class out of range', a))
        errors_by_code[code] += 1
        continue
    for d, (allowed, kind, successor, arrival) in enumerate(row(code)):
        index = a*4+d
        failures = []
        if kind != rep_rows[a][d][1]:
            all_direction_kind_errors.append((code, a, d, kind, rep_rows[a][d][1]))
        if (dests[index] != 0) != allowed:
            failures.append('admissibility')
        if allowed:
            if kinds[index] != kind:
                failures.append('kind')
            if dests[index] != classes[successor]+1:
                failures.append('successor')
            if kind != 2 and reps[a] % 4 != arrival:
                failures.append('arrival')
        if failures:
            row_errors.append((code, a, d, failures))
            errors_by_code[code] += 1

table_shape_errors = [i for i, (dest, kind) in enumerate(zip(dests, kinds))
                      if dest > 3741 or ((dest == 0) != (kind == 3)) or
                      (dest != 0 and kind >= 3)]
edge_counts = Counter(k for dest, k in zip(dests, kinds) if dest != 0)
targets = []
for i in range(80, 85):
    name = f'rawClass_{i}'
    offset = offsets['rawClass'][name]
    end = offset + 16384
    low_code, high_code = offset // 12, (end-1) // 12
    target_valid = sorted(valid.intersection(range(low_code, high_code+1)))
    target_errors = [e for e in row_errors if low_code <= e[0] <= high_code]
    targets.append({
        'declaration': name,
        'line': 15+2*i,
        'bit_offset': offset,
        'end_bit_exclusive': end,
        'first_code': low_code,
        'last_code': high_code,
        'first_lane_start_bit_in_chunk': low_code*12-offset,
        'last_lane_end_bit_past_chunk': (high_code+1)*12-end,
        'valid_words': len(target_valid),
        'invalid_words': high_code-low_code+1-len(target_valid),
        'classes_on_valid_words': len({classes[c] for c in target_valid}),
        'coverage_errors': [c for c in coverage_errors if low_code <= c <= high_code],
        'row_error_count': len(target_errors),
        'first_row_errors': target_errors[:5],
        'literal_sha256_hex_ascii': hashlib.sha256(format(literals[name], 'x').encode()).hexdigest(),
        'sample_valid_words': [(c, classes[c]) for c in target_valid[:3]],
    })

result = {
    'source_sha256': hashlib.sha256(text.encode()).hexdigest(),
    'packing_bit_lengths': {name: value.bit_length() for name, value in packed.items()},
    'raw_chunk_count': len(offsets['rawClass']),
    'raw_chunks_all_used': set(offsets['rawClass']) == {f'rawClass_{i}' for i in range(768)},
    'depth_counts': depth_counts,
    'coverage_error_count': len(coverage_errors),
    'first_coverage_errors': coverage_errors[:10],
    'representative_error_count': len(representative_errors),
    'first_representative_errors': representative_errors[:10],
    'table_shape_error_count': len(table_shape_errors),
    'row_error_count': len(row_errors),
    'first_row_errors': row_errors[:10],
    'all_direction_kind_error_count': len(all_direction_kind_errors),
    'first_all_direction_kind_errors': all_direction_kind_errors[:10],
    'edge_counts': dict(edge_counts),
    'targets': targets,
}
print(json.dumps(result, indent=2))
