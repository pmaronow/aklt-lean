"""Read-only reconstruction of the Lean literal tables and paper's raw model."""
from collections import Counter
from pathlib import Path
import json
import re

SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
source = SOURCE.read_text()
literals = {
    name: (int(h, 16), len(h) * 4)
    for name, h in re.findall(
        r'^private noncomputable def (\w+) : ℕ := 0x([0-9a-f]+)$', source, re.M
    )
}


def packed(name):
    expr = re.search(rf'^noncomputable def {name} : ℕ := (.*)$', source, re.M)[1]
    tokens = re.findall(r'\w+|<<<|[()+]', expr)
    assert ''.join(tokens) == re.sub(r'\s+', '', expr)
    pos = 0

    def atom():
        nonlocal pos
        t = tokens[pos]
        pos += 1
        if t == '(':
            value, offsets = expression()
            assert tokens[pos] == ')'
            pos += 1
            return value, offsets
        assert t in literals
        return literals[t][0], {t: 0}

    def expression():
        nonlocal pos
        value, offsets = atom()
        while pos < len(tokens) and tokens[pos] != ')':
            op = tokens[pos]
            pos += 1
            if op == '<<<':
                shift = int(tokens[pos])
                pos += 1
                value <<= shift
                offsets = {k: v + shift for k, v in offsets.items()}
            else:
                assert op == '+'
                rhs, right_offsets = atom()
                assert not (offsets.keys() & right_offsets.keys())
                value += rhs
                offsets.update(right_offsets)
        return value, offsets

    value, offsets = expression()
    assert pos == len(tokens)
    # Verify that all additions join disjoint adjacent literal fields.
    end = 0
    for key, offset in sorted(offsets.items(), key=lambda item: item[1]):
        assert offset == end, (key, offset, end)
        assert literals[key][0] < 1 << literals[key][1]
        end += literals[key][1]
    return value, offsets, end


tables = {name: packed(name) for name in
          ('rawClass', 'representatives', 'destinations', 'edgeKinds')}
assert set(literals) == set().union(*(table[1].keys() for table in tables.values()))


def lanes(name, width, count):
    value, _, bits = tables[name]
    # Leading zero hex digits (including zero destination lanes) can be omitted.
    assert bits <= width * count, (name, bits, width * count)
    # Decode from low bits; byte extraction avoids repeatedly shifting a huge int.
    data = value.to_bytes((width * count + 7) // 8 + 3, 'little')
    mask = (1 << width) - 1
    return [int.from_bytes(data[(i * width) // 8:(i * width) // 8 + 4], 'little')
            >> ((i * width) % 8) & mask for i in range(count)]


N = 4 ** 10
Q = 3741
raw_class = lanes('rawClass', 12, N)
reps = lanes('representatives', 20, Q)
dest = lanes('destinations', 12, 4 * Q)
kinds = lanes('edgeKinds', 2, 4 * Q)
steps = ((1, 0), (0, 1), (-1, 0), (0, -1))


def decode(code):
    return tuple((code >> (2 * (9 - i))) & 3 for i in range(10))


def model(code):
    word = decode(code)
    vertices = [(0, 0)]
    bonds = set()
    for d in word:
        x, y = vertices[-1]
        dx, dy = steps[d]
        new = (x + dx, y + dy)
        bond = frozenset((vertices[-1], new))
        assert bond not in bonds, code
        bonds.add(bond)
        vertices.append(new)
    rows = []
    for d, (dx, dy) in enumerate(steps):
        x, y = vertices[-1]
        new = (x + dx, y + dy)
        allowed = d != (word[-1] + 2) % 4 and frozenset((vertices[-1], new)) not in bonds
        kind = 2 if vertices[-1] in vertices[:-1] else (0 if d == word[-1] else 1)
        successor = ((code & (4 ** 9 - 1)) << 2) | d
        rows.append((allowed, kind, successor))
    return word, rows


valid = set()
depth_counts = Counter()


def generate(code, depth, position, bonds):
    depth_counts[depth] += 1
    if depth == 10:
        valid.add(code)
        return
    x, y = position
    for d, (dx, dy) in enumerate(steps):
        new = (x + dx, y + dy)
        bond = frozenset((position, new))
        if bond not in bonds:
            generate(4 * code + d, depth + 1, new, bonds | {bond})


generate(0, 0, (0, 0), set())
assert len(valid) == 60092
coverage_errors = [code for code, a in enumerate(raw_class)
                   if a > Q or ((a < Q) != (code in valid))]
representative_errors = [a for a, code in enumerate(reps)
                         if code not in valid or raw_class[code] != a]
encoding_errors = [i for i in range(4 * Q)
                   if dest[i] > Q or ((dest[i] == 0) != (kinds[i] == 3))
                   or (dest[i] != 0 and kinds[i] >= 3)]
row_errors = []
representative_models = {a: model(code) for a, code in enumerate(reps)}
for code in sorted(valid):
    a = raw_class[code]
    if a >= Q:
        row_errors.append((code, 'invalid class', a))
        continue
    word, rows = model(code)
    rep_word, rep_rows = representative_models[a]
    for d, (allowed, kind, successor) in enumerate(rows):
        i = 4 * a + d
        if (allowed, kind) != rep_rows[d][:2]:
            row_errors.append((code, d, 'raw versus representative admissibility/kind', a))
        if allowed != (dest[i] != 0):
            row_errors.append((code, d, 'admissibility', a))
        if allowed:
            if kinds[i] != kind:
                row_errors.append((code, d, 'kind', a))
            if dest[i] - 1 != raw_class[successor]:
                row_errors.append((code, d, 'successor', a, successor))
            if kind != 2 and word[-1] != rep_word[-1]:
                row_errors.append((code, d, 'arrival', a))

targets = []
for k in range(255, 260):
    name = f'rawClass_{k}'
    low = tables['rawClass'][1][name]
    high = low + literals[name][1] - 1
    first, last = low // 12, high // 12
    interior_first, interior_last = (low + 11) // 12, (high + 1) // 12 - 1
    target_codes = range(first, last + 1)
    relevant_rows = [e for e in row_errors if first <= e[0] <= last]
    # Include incoming successor images too, since a changed class entry can break these.
    incoming_errors = [e for e in row_errors if e[2] == 'successor' and first <= e[4] <= last]
    targets.append({
        'name': name, 'lean_line': 15 + 2 * k,
        'bit_interval_inclusive': [low, high],
        'code_interval_inclusive': [first, last],
        'fully_contained_code_interval': [interior_first, interior_last],
        'valid_codes': sum(c in valid for c in target_codes),
        'class_entry_range': [min(raw_class[c] for c in target_codes), max(raw_class[c] for c in target_codes)],
        'coverage_errors': [c for c in coverage_errors if first <= c <= last],
        'outgoing_errors': relevant_rows,
        'incoming_errors': incoming_errors,
        'first_valid_examples': [(c, ''.join('ENWS'[d] for d in decode(c)), raw_class[c])
                                 for c in target_codes if c in valid][:3],
    })

result = {
    'literal_declarations': len(literals),
    'table_bits': {name: t[2] for name, t in tables.items()},
    'depth_counts': dict(sorted(depth_counts.items())),
    'class_entry_counts': dict(sorted(Counter(raw_class).items())) if coverage_errors else 'all 60092 valid codes have classes below 3741; all other codes have sentinel 3741',
    'coverage_error_count': len(coverage_errors),
    'coverage_error_examples': coverage_errors[:10],
    'representative_error_count': len(representative_errors),
    'representative_error_examples': representative_errors[:10],
    'encoding_error_count': len(encoding_errors),
    'row_error_count': len(row_errors),
    'row_error_examples': row_errors[:10],
    'edge_counts': dict(sorted(Counter(kinds[i] for i in range(4 * Q) if dest[i]).items())),
    'targets': targets,
}
Path('audit_results.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({k: v for k, v in result.items() if k != 'class_entry_counts'}, indent=2))
