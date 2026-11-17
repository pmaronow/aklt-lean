"""Independently check the packed data against the paper's raw-trail model.

Reads only the authorized Lean input. No archived data or export program is used.
"""

import ast
from array import array
from collections import Counter
import hashlib
import json
from pathlib import Path
import re


SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
source = SOURCE.read_text()
literals = {}
literal_lines = {}
for line_no, line in enumerate(source.splitlines(), 1):
    match = re.fullmatch(r'private noncomputable def (\w+) : ℕ := 0x([0-9a-f]+)', line)
    if match:
        name, digits = match.groups()
        literals[name] = int(digits, 16)
        literal_lines[name] = line_no
assert len(literals) == 786


def read_assembly(name):
    expression = re.search(rf'^noncomputable def {name} : ℕ := (.+)$', source, re.M).group(1)
    node = ast.parse(expression.replace('<<<', '<<'), mode='eval').body

    def evaluate(node):
        if isinstance(node, ast.Name):
            return literals[node.id], {node.id: 0}
        assert isinstance(node, ast.BinOp)
        if isinstance(node.op, ast.LShift):
            assert isinstance(node.right, ast.Constant) and isinstance(node.right.value, int)
            value, offsets = evaluate(node.left)
            shift = node.right.value
            return value << shift, {key: offset + shift for key, offset in offsets.items()}
        assert isinstance(node.op, ast.Add)
        left, loffsets = evaluate(node.left)
        right, roffsets = evaluate(node.right)
        assert not loffsets.keys() & roffsets.keys()
        return left + right, loffsets | roffsets

    packed, offsets = evaluate(node)
    ordered = sorted(offsets, key=offsets.get)
    for lower, upper in zip(ordered, ordered[1:]):
        assert offsets[lower] + literals[lower].bit_length() <= offsets[upper]
    assert offsets[ordered[0]] == 0
    return packed, offsets


raw, offsets = read_assembly('rawClass')
representatives, _ = read_assembly('representatives')
destinations, _ = read_assembly('destinations')
kinds, _ = read_assembly('edgeKinds')
assert len(offsets) == 768
assert sorted(offsets, key=offsets.get, reverse=True) == [f'rawClass_{i}' for i in range(768)]
assert all(offsets[f'rawClass_{i}'] == (767 - i) * 16384 - 4 for i in range(767))
assert offsets['rawClass_767'] == 0


def lanes(packed, width, count):
    # Use bytes to avoid repeatedly shifting a 12-million-bit integer.
    data = packed.to_bytes((width * count + 7) // 8, 'little')
    result = array('H' if width <= 16 else 'I')
    for index in range(count):
        bit = width * index
        first, shift = divmod(bit, 8)
        length = (shift + width + 7) // 8
        value = int.from_bytes(data[first:first + length], 'little') >> shift
        result.append(value & ((1 << width) - 1))
    return result


classes = lanes(raw, 12, 4**10)
reps = lanes(representatives, 20, 3741)
dest = lanes(destinations, 12, 3741 * 4)
kind = lanes(kinds, 2, 3741 * 4)
assert max(classes) == 3741
assert max(reps) < 4**10
assert max(dest) == 3741
assert all((d == 0) == (k == 3) for d, k in zip(dest, kind))

STEPS = ((1, 0), (0, 1), (-1, 0), (0, -1))


def bond(a, b):
    return tuple(sorted((a, b)))


def generate(depth, code, vertices, bonds):
    if depth == 10:
        yield code, vertices, bonds
        return
    x, y = vertices[-1]
    for d, (dx, dy) in enumerate(STEPS):
        next_vertex = x + dx, y + dy
        next_bond = bond(vertices[-1], next_vertex)
        if next_bond not in bonds:
            yield from generate(depth + 1, code * 4 + d,
                                vertices + (next_vertex,), bonds | {next_bond})


def model_row(code, vertices, bonds):
    arrival = code % 4
    endpoint = vertices[-1]
    revisit = endpoint in vertices[:-1]
    row = []
    for d, (dx, dy) in enumerate(STEPS):
        next_vertex = endpoint[0] + dx, endpoint[1] + dy
        admissible = d != (arrival + 2) % 4 and bond(endpoint, next_vertex) not in bonds
        step_kind = 2 if revisit else (0 if d == arrival else 1)
        successor = (code % 4**9) * 4 + d
        row.append((admissible, step_kind, successor))
    return row


raw_codes = bytearray(4**10)
class_counts = Counter()
regenerated_rows = {}
representative_rows = {}
reps_set = set(reps)
for code, vertices, bonds in generate(0, 0, ((0, 0),), frozenset()):
    raw_codes[code] = 1
    a = classes[code]
    assert a < 3741, ('raw assigned invalid sentinel', code, a)
    class_counts[a] += 1
    row = model_row(code, vertices, bonds)
    regenerated_rows[code] = row
    if code in reps_set:
        representative_rows[code] = row
    for d, (admissible, step_kind, successor) in enumerate(row):
        index = a * 4 + d
        assert (dest[index] != 0) == admissible, ('admissibility', code, a, d)
        if admissible:
            assert kind[index] == step_kind, ('kind', code, a, d)
            assert classes[successor] < 3741, ('successor raw coverage', code, d)
            assert dest[index] == classes[successor] + 1, ('successor', code, a, d)
            if step_kind != 2:
                assert code % 4 == reps[a] % 4, ('arrival', code, a, d)

assert sum(raw_codes) == 60092
assert len(class_counts) == 3741
assert len(reps_set) == 3741
assert len(representative_rows) == 3741
for code, a in enumerate(classes):
    assert (a < 3741) == bool(raw_codes[code]), ('coverage', code, a)
for a, code in enumerate(reps):
    assert raw_codes[code] and classes[code] == a, ('representative', a, code)
for code, row in regenerated_rows.items():
    representative_row = representative_rows[reps[classes[code]]]
    for entry, rep_entry in zip(row, representative_row):
        assert entry[:2] == rep_entry[:2], ('same class admissibility/kind', code)
edge_counts = Counter(kind[index] for index, destination in enumerate(dest) if destination)
assert dict(edge_counts) == {0: 2516, 1: 5032, 2: 1872}

targets = []
for i in range(170, 175):
    name = f'rawClass_{i}'
    offset = offsets[name]
    first_code = offset // 12
    last_code = (offset + 16384 - 1) // 12
    affected = range(first_code, last_code + 1)
    valid = [code for code in affected if raw_codes[code]]
    targets.append({
        'declaration': name,
        'line': literal_lines[name],
        'bit_offset': offset,
        'bit_interval_inclusive': [offset, offset + 16383],
        'affected_code_interval_inclusive': [first_code, last_code],
        'affected_codes': len(affected),
        'raw_windows': len(valid),
        'invalid_words': len(affected) - len(valid),
        'class_range_on_raw': [min(classes[c] for c in valid), max(classes[c] for c in valid)] if valid else None,
        'literal_hex_sha256': hashlib.sha256(format(literals[name], 'x').encode()).hexdigest(),
    })

result = {
    'source_sha256': hashlib.sha256(source.encode()).hexdigest(),
    'literal_count': len(literals),
    'raw_class_chunks': len(offsets),
    'raw_table_bit_length': raw.bit_length(),
    'raw_code_domain': len(classes),
    'raw_windows': sum(raw_codes),
    'nonempty_classes': len(class_counts),
    'representatives': len(reps_set),
    'admitted_edges_by_kind': dict(edge_counts),
    'raw_labelled_directions_checked': len(regenerated_rows) * 4,
    'checks': 'All coverage, class-range, representative, admissibility, kind, successor, final-direction, and edge-count assertions passed.',
    'targets': targets,
}
Path('audit_results.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
