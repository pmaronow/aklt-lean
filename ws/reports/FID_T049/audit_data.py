"""Independent finite check of the supplied Lean literal class-map chunks."""
import ast
import json
import re
from collections import Counter
from pathlib import Path

SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
text = SOURCE.read_text()
values, expressions, line_numbers = {}, {}, {}
for line_number, line in enumerate(text.splitlines(), 1):
    match = re.fullmatch(r'(?:private )?noncomputable def (\w+) : ℕ := (.+)', line)
    if match:
        name, expression = match.groups()
        expressions[name] = ast.parse(expression.replace('<<<', '<<'), mode='eval').body
        line_numbers[name] = line_number
        if expression.startswith('0x'):
            values[name] = int(expression, 16)


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


def leaves(node, offset=0):
    if isinstance(node, ast.Name):
        return [(node.id, offset)]
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add):
        return leaves(node.left, offset) + leaves(node.right, offset)
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.LShift):
        return leaves(node.left, offset + evaluate(node.right))
    raise ValueError(ast.dump(node))


def unpack(name, width, count):
    values[name] = evaluate(expressions[name])
    packed = values[name].to_bytes((width * count + 7) // 8, 'little') + bytes(4)
    result = []
    for index in range(count):
        bit = width * index
        byte, remainder = divmod(bit, 8)
        word = int.from_bytes(packed[byte:byte + 4], 'little')
        result.append((word >> remainder) & ((1 << width) - 1))
    return result


classes = unpack('rawClass', 12, 4**10)
representatives = unpack('representatives', 20, 3741)
destinations = unpack('destinations', 12, 4 * 3741)
kinds = unpack('edgeKinds', 2, 4 * 3741)

# Check every literal is within the bit allocation in the assembled expression.
packing = {}
for name in ('rawClass', 'representatives', 'destinations', 'edgeKinds'):
    entries = sorted(leaves(expressions[name]), key=lambda pair: pair[1])
    assert len({key for key, _ in entries}) == len(entries)
    for index, (key, offset) in enumerate(entries):
        if index + 1 < len(entries):
            assert values[key].bit_length() <= entries[index + 1][1] - offset
    packing[name] = {'chunks': len(entries), 'bits': values[name].bit_length()}
assert set(key for key, _ in leaves(expressions['rawClass'])) == {
    f'rawClass_{i}' for i in range(768)
}

steps = ((1, 0), (0, 1), (-1, 0), (0, -1))


def translate(point, direction):
    dx, dy = steps[direction]
    return point[0] + dx, point[1] + dy


def bond(a, b):
    return tuple(sorted((a, b)))


def decode(code):
    return tuple((code >> (2 * (9 - index))) & 3 for index in range(10))


def geometry(word):
    vertices = [(0, 0)]
    bonds = []
    for direction in word:
        end = translate(vertices[-1], direction)
        bonds.append(bond(vertices[-1], end))
        vertices.append(end)
    return vertices, bonds


# Enumerate directly from the paper's unused-unoriented-bond recursion.
windows = {}
level_counts = Counter()


def enumerate_windows(word=(), code=0, vertices=((0, 0),), bonds=frozenset()):
    level_counts[len(word)] += 1
    if len(word) == 10:
        windows[code] = (word, vertices, bonds)
        return
    for direction in range(4):
        end = translate(vertices[-1], direction)
        edge = bond(vertices[-1], end)
        if edge not in bonds:
            enumerate_windows(word + (direction,), 4 * code + direction,
                              vertices + (end,), bonds | {edge})


enumerate_windows()
failures = []


def check(condition, *description):
    if not condition:
        failures.append(description)


check(len(windows) == 60092, 'window_count', len(windows))
for code, class_number in enumerate(classes):
    check(class_number <= 3741, 'class_range', code, class_number)
    check((class_number < 3741) == (code in windows), 'coverage', code, class_number)

for class_number, code in enumerate(representatives):
    check(code < 4**10, 'representative_range', class_number, code)
    check(code in windows, 'representative_raw', class_number, code)
    check(classes[code] == class_number, 'representative_projection', class_number, code)

for edge_index, (destination, kind) in enumerate(zip(destinations, kinds)):
    check(destination <= 3741, 'destination_range', edge_index, destination)
    check((destination == 0) == (kind == 3), 'edge_sentinel', edge_index)
    check(destination == 0 or kind < 3, 'kind_range', edge_index)

raw_checks, admitted_checks = 0, 0
for code, (word, vertices, bonds) in windows.items():
    class_number = classes[code]
    if class_number >= 3741:
        continue
    for direction in range(4):
        raw_checks += 1
        edge_index = 4 * class_number + direction
        admissible = (direction != (word[-1] + 2) % 4 and
                      bond(vertices[-1], translate(vertices[-1], direction)) not in bonds)
        check((destinations[edge_index] != 0) == admissible,
              'admissibility', code, class_number, direction)
        if admissible:
            admitted_checks += 1
            kind = 2 if vertices[-1] in vertices[:-1] else (0 if direction == word[-1] else 1)
            check(kinds[edge_index] == kind, 'kind', code, class_number, direction)
            successor = (code % (4**9)) * 4 + direction
            check(destinations[edge_index] - 1 == classes[successor],
                  'successor', code, class_number, direction)
            if kind != 2:
                check(representatives[class_number] % 4 == word[-1],
                      'arrival', code, class_number, direction)

# This also checks the stronger classwise kind/arrival compatibility in the paper's lemma.
for code, (word, vertices, bonds) in windows.items():
    class_number = classes[code]
    if class_number >= 3741:
        continue
    rep_word, rep_vertices, rep_bonds = windows[representatives[class_number]]
    for direction in range(4):
        kind = 2 if vertices[-1] in vertices[:-1] else (0 if direction == word[-1] else 1)
        rep_kind = 2 if rep_vertices[-1] in rep_vertices[:-1] else (0 if direction == rep_word[-1] else 1)
        check(kind == rep_kind, 'classwise_kind', code, class_number, direction)

edge_counts = Counter(kind for destination, kind in zip(destinations, kinds) if destination != 0)
check(dict(edge_counts) == {0: 2516, 1: 5032, 2: 1872}, 'edge_counts', dict(edge_counts))

chunk_results = {}
offsets = dict(leaves(expressions['rawClass']))
for index in range(210, 215):
    name = f'rawClass_{index}'
    offset = offsets[name]
    low_code, high_code = offset // 12, (offset + 16384 - 1) // 12
    selected = range(low_code, high_code + 1)
    raw_codes = [code for code in selected if code in windows]
    relevant_failures = [failure for failure in failures
                         if len(failure) > 1 and isinstance(failure[1], int)
                         and low_code <= failure[1] <= high_code]
    chunk_results[name] = {
        'line': line_numbers[name], 'bit_offset': offset,
        'bit_length': values[name].bit_length(),
        'affected_codes': [low_code, high_code],
        'raw_codes': len(raw_codes), 'nonraw_codes': len(selected) - len(raw_codes),
        'classes': len({classes[code] for code in raw_codes}),
        'admissible_edges': sum(destinations[4 * classes[code] + d] != 0
                                for code in raw_codes for d in range(4)),
        'first_raw': [[code, classes[code]] for code in raw_codes[:3]],
        'last_raw': [[code, classes[code]] for code in raw_codes[-3:]],
        'failures': relevant_failures[:10],
    }

result = {
    'packing': packing, 'level_counts': dict(sorted(level_counts.items())),
    'class_value_counts': {'valid': sum(c < 3741 for c in classes),
                           'sentinel': classes.count(3741)},
    'raw_direction_checks': raw_checks, 'admitted_checks': admitted_checks,
    'edge_counts': dict(edge_counts), 'chunks': chunk_results,
    'failure_count': len(failures), 'first_failures': failures[:30],
}
Path('audit_results.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
assert not failures
