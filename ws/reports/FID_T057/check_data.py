"""Read-only reconstruction of the Lean literals and the paper's finite check.

Reads only the permitted Lean input file; writes a small JSON result locally.
No Lean process or external archived witness is used.
"""
import ast
from collections import Counter
import hashlib
import json
from pathlib import Path
import re

ROOT = Path('/home/ubuntu/aklt/reports/FID_T057')
SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
text = SOURCE.read_text()
values = {}
expressions = {}
locations = {}


def evaluate(node):
    if isinstance(node, ast.Constant) and isinstance(node.value, int):
        return node.value
    if isinstance(node, ast.Name):
        return values[node.id]
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add):
        return evaluate(node.left) + evaluate(node.right)
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.LShift):
        return evaluate(node.left) << evaluate(node.right)
    raise ValueError(ast.dump(node))


for line, content in enumerate(text.splitlines(), 1):
    match = re.fullmatch(r'(?:private )?noncomputable def (\w+) : ℕ := (.*)', content)
    if match:
        name, expression = match.groups()
        node = ast.parse(expression.replace('<<<', '<<'), mode='eval').body
        expressions[name] = node
        values[name] = evaluate(node)
        locations[name] = line


def leaves(node, offset=0):
    if isinstance(node, ast.Name):
        return [(node.id, offset)]
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add):
        return leaves(node.left, offset) + leaves(node.right, offset)
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.LShift):
        return leaves(node.left, offset + evaluate(node.right))
    raise ValueError(ast.dump(node))


# Verify each concatenation uses every literal exactly once, without overlap.
layouts = {}
widths = {'rawClass': 12 * 4**10, 'representatives': 20 * 3741,
          'destinations': 12 * 3741 * 4, 'edgeKinds': 2 * 3741 * 4}
for name, width in widths.items():
    layout = sorted(leaves(expressions[name]), key=lambda item: item[1])
    assert layout[0][1] == 0
    expected = {n for n in values if re.fullmatch(name + r'_\d+', n)}
    assert Counter(n for n, _ in layout) == Counter({n: 1 for n in expected})
    for i, (chunk, offset) in enumerate(layout):
        end = layout[i + 1][1] if i + 1 < len(layout) else width
        # The most significant chunk may be followed by implicit zero padding.
        assert 0 < end - offset
        assert end - offset <= 16384 or i + 1 == len(layout)
        assert values[chunk].bit_length() <= end - offset
    assert values[name].bit_length() <= width
    layouts[name] = dict(layout)


def unpack(name, width, count):
    # byte conversion avoids repeatedly shifting the 12-million-bit raw table.
    blob = values[name].to_bytes((width * count + 7) // 8, 'little')
    mask = (1 << width) - 1
    return [((int.from_bytes(blob[(width * i) // 8:(width * i) // 8 + 4],
                            'little') >> ((width * i) % 8)) & mask)
            for i in range(count)]


classes = unpack('rawClass', 12, 4**10)
representatives = unpack('representatives', 20, 3741)
destinations = unpack('destinations', 12, 3741 * 4)
kinds = unpack('edgeKinds', 2, 3741 * 4)

steps = [(1, 0), (0, 1), (-1, 0), (0, -1)]
counts = [0] * 11
raw = {}


def bond(a, b):
    return tuple(sorted((a, b)))


def generate(word=(), code=0, endpoint=(0, 0), used=frozenset(), departures=frozenset()):
    n = len(word)
    counts[n] += 1
    if n == 10:
        raw[code] = (word, endpoint, used, departures)
        return
    for d, (dx, dy) in enumerate(steps):
        new = (endpoint[0] + dx, endpoint[1] + dy)
        edge = bond(endpoint, new)
        if edge not in used:
            generate(word + (d,), code * 4 + d, new, used | {edge}, departures | {endpoint})


generate()
assert counts[1:] == [4, 12, 36, 108, 316, 916, 2628, 7500, 21268, 60092]
coverage_failures = [code for code, cls in enumerate(classes)
                     if not (cls <= 3741 and ((cls < 3741) == (code in raw)))]
representative_failures = [a for a, code in enumerate(representatives)
                           if not (code < 4**10 and code in raw and classes[code] == a)]
storage_failures = [i for i, (dest, kind) in enumerate(zip(destinations, kinds))
                    if not (dest <= 3741 and ((dest == 0) == (kind == 3))
                            and (dest == 0 or kind < 3))]
row_failures = []
checked_admitted = 0
for code, (word, endpoint, used, departures) in raw.items():
    cls = classes[code]
    if cls >= 3741:
        row_failures.append((code, 'invalid class', cls))
        continue
    rep_word, rep_endpoint, _, rep_departures = raw[representatives[cls]]
    for d, (dx, dy) in enumerate(steps):
        # The paper also asks for identical kind on inadmissible directions.
        kind = 2 if endpoint in departures else (0 if d == word[-1] else 1)
        rep_kind = (2 if rep_endpoint in rep_departures
                    else (0 if d == rep_word[-1] else 1))
        if kind != rep_kind:
            row_failures.append((code, d, 'representative kind'))
        admitted = (d != (word[-1] + 2) % 4
                    and bond(endpoint, (endpoint[0] + dx, endpoint[1] + dy)) not in used)
        idx = cls * 4 + d
        if admitted != (destinations[idx] != 0):
            row_failures.append((code, d, 'admissibility'))
        if admitted:
            checked_admitted += 1
            successor = ((code % 4**9) * 4) + d
            if kinds[idx] != kind:
                row_failures.append((code, d, 'kind'))
            if successor not in raw or destinations[idx] - 1 != classes[successor]:
                row_failures.append((code, d, 'successor'))
            if kind != 2 and representatives[cls] % 4 != word[-1]:
                row_failures.append((code, d, 'arrival'))

edge_counts = Counter(kind for dest, kind in zip(destinations, kinds) if dest != 0)
targets = {}
for i in range(250, 255):
    name = f'rawClass_{i}'
    start = layouts['rawClass'][name]
    end = start + 16384
    first, last = start // 12, (end - 1) // 12
    codes = range(first, last + 1)
    valid = [code for code in codes if code in raw]
    failures = [code for code in coverage_failures if first <= code <= last]
    row_errors = [r for r in row_failures if first <= r[0] <= last]
    literal = re.search(rf'def {name} : ℕ := 0x([0-9a-f]+)', text).group(1)
    targets[name] = {
        'line': locations[name], 'hex_digits': len(literal),
        'literal_sha256_bytes': hashlib.sha256(bytes.fromhex(literal)).hexdigest(),
        'bit_interval_inclusive': [start, end - 1],
        'code_interval_inclusive': [first, last],
        'lanes_touched': last - first + 1,
        'full_lanes': sum(start <= 12 * c and 12 * (c + 1) <= end for c in codes),
        'valid_raw_lanes': len(valid), 'sentinel_lanes': last - first + 1 - len(valid),
        'distinct_classes': len({classes[c] for c in valid}),
        'coverage_failures': failures, 'row_failures': row_errors,
        'boundary_lanes': {str(c): classes[c] for c in [first, last]},
    }

result = {
    'parsed_natural_definitions': len(values),
    'raw_literal_chunks': len(layouts['rawClass']),
    'concatenation_widths': widths,
    'raw_counts_by_length': counts,
    'raw_table_lanes': len(classes),
    'valid_raw_lanes': len(raw), 'invalid_sentinel_lanes': len(classes) - len(raw),
    'coverage_failure_count': len(coverage_failures),
    'representative_failure_count': len(representative_failures),
    'storage_failure_count': len(storage_failures),
    'row_failure_count': len(row_failures), 'row_failure_examples': row_failures[:10],
    'raw_admitted_transitions_checked': checked_admitted,
    'quotient_edge_counts_kind_0_1_2': [edge_counts[k] for k in range(3)],
    'targets': targets,
}
(ROOT / 'check_results.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
assert not (coverage_failures or representative_failures or storage_failures or row_failures)
assert [edge_counts[k] for k in range(3)] == [2516, 5032, 1872]
