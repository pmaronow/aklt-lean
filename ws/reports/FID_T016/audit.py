"""Independent finite audit of the supplied Lean literals against p:automaton10.

Reads only the authorized Lean input. This is a Python check, not a Lean proof.
"""
from pathlib import Path
from collections import Counter
import json
import re

SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
source = SOURCE.read_text()
literal_matches = list(re.finditer(
    r'^private noncomputable def (\w+) : ℕ := (0x[0-9a-f]+)$', source, re.M))
literals = {m[1]: int(m[2], 16) for m in literal_matches}


def packed(name):
    expression = re.search(
        rf'^noncomputable def {name} : ℕ := (.*)$', source, re.M)[1]
    tokens = re.findall(r'\w+|<<<|[()+]', expression)
    assert ''.join(tokens) == re.sub(r'\s+', '', expression)
    cursor = 0

    def atom():
        nonlocal cursor
        tok = tokens[cursor]
        cursor += 1
        if tok == '(':
            out = expr()
            assert tokens[cursor] == ')'
            cursor += 1
            return out
        return int(tok) if tok.isdigit() else [(tok, 0)]

    def expr():
        nonlocal cursor
        out = atom()
        # The exporter parenthesizes every binary expression.
        if cursor < len(tokens) and tokens[cursor] in ('+', '<<<'):
            op = tokens[cursor]
            cursor += 1
            rhs = atom()
            if op == '+':
                assert isinstance(out, list) and isinstance(rhs, list)
                out = out + rhs
            else:
                assert isinstance(out, list) and isinstance(rhs, int)
                out = [(key, offset + rhs) for key, offset in out]
        return out

    terms = expr()
    assert cursor == len(tokens)
    assert len({key for key, _ in terms}) == len(terms)
    ordered = sorted(terms, key=lambda term: term[1])
    for (key, off), (_, next_off) in zip(ordered, ordered[1:]):
        assert literals[key].bit_length() <= next_off - off
    value = sum(literals[key] << off for key, off in terms)
    return value, dict(terms)


def lanes(value, width, length):
    assert value.bit_length() <= width * length
    if width % 4 == 0:
        hex_width = width // 4
        h = format(value, f'0{hex_width * length}x')
        return [int(h[i:i + hex_width], 16)
                for i in range(len(h) - hex_width, -1, -hex_width)]
    raw_bytes = value.to_bytes((width * length + 7) // 8, 'little')
    return [(raw_bytes[(width * i) // 8] >> ((width * i) % 8)) & ((1 << width) - 1)
            for i in range(length)]


raw_value, offsets = packed('rawClass')
raw = lanes(raw_value, 12, 4**10)
reps = lanes(packed('representatives')[0], 20, 3741)
dest = lanes(packed('destinations')[0], 12, 4 * 3741)
kinds = lanes(packed('edgeKinds')[0], 2, 4 * 3741)
steps = ((1, 0), (0, 1), (-1, 0), (0, -1))
labels = 'ENWS'


def edge(x, y):
    return tuple(sorted((x, y)))


def digits(code):
    return tuple((code >> (2 * (9 - i))) & 3 for i in range(10))


def geometry(code):
    directions = digits(code)
    vertices = [(0, 0)]
    bonds = []
    for d in directions:
        x, y = vertices[-1]
        dx, dy = steps[d]
        z = x + dx, y + dy
        bonds.append(edge(vertices[-1], z))
        vertices.append(z)
    return directions, vertices, set(bonds)


def transitions(code):
    ds, vs, bonds = geometry(code)
    arrival = ds[-1]
    revisit = vs[-1] in vs[:-1]
    out = []
    for d, (dx, dy) in enumerate(steps):
        z = vs[-1][0] + dx, vs[-1][1] + dy
        allowed = d != (arrival + 2) % 4 and edge(vs[-1], z) not in bonds
        kind = 2 if revisit else (0 if d == arrival else 1)
        successor = ((code % 4**9) * 4) + d
        out.append((allowed, kind, successor))
    return arrival, out


raw_codes = set()
counts = Counter()


def generate(depth, code, current, used):
    counts[depth] += 1
    if depth == 10:
        raw_codes.add(code)
        return
    for d, (dx, dy) in enumerate(steps):
        nxt = current[0] + dx, current[1] + dy
        bond = edge(current, nxt)
        if bond in used:
            continue
        used.add(bond)
        generate(depth + 1, code * 4 + d, nxt, used)
        used.remove(bond)


generate(0, 0, (0, 0), set())
assert [counts[i] for i in range(1, 11)] == [4, 12, 36, 108, 316, 916, 2628, 7500, 21268, 60092]
coverage_errors = [(code, a, code in raw_codes) for code, a in enumerate(raw)
                   if a > 3741 or ((a < 3741) != (code in raw_codes))]
representative_errors = [(a, code, raw[code] if code < 4**10 else None)
                         for a, code in enumerate(reps)
                         if code >= 4**10 or code not in raw_codes or raw[code] != a]
row_errors = []
for a, code in enumerate(reps):
    arrival, ts = transitions(code)
    for d, (allowed, kind, successor) in enumerate(ts):
        ix = 4 * a + d
        expected_dest = raw[successor] + 1 if allowed else 0
        expected_kind = kind if allowed else 3
        if dest[ix] != expected_dest or kinds[ix] != expected_kind:
            row_errors.append((a, code, labels[d], dest[ix], expected_dest, kinds[ix], expected_kind))

compatibility_errors = []
all_direction_kind_errors = []
for code in sorted(raw_codes):
    a = raw[code]
    if a >= 3741:
        continue
    arrival, ts = transitions(code)
    rep_arrival = reps[a] % 4
    _, rep_ts = transitions(reps[a])
    for d, (allowed, kind, successor) in enumerate(ts):
        ix = 4 * a + d
        if kind != rep_ts[d][1]:
            all_direction_kind_errors.append((code, a, labels[d], kind, rep_ts[d][1]))
        if (allowed != (dest[ix] != 0)
                or (allowed and (kinds[ix] != kind or dest[ix] != raw[successor] + 1
                                 or (kind != 2 and arrival != rep_arrival)))):
            compatibility_errors.append((code, a, labels[d], allowed, kind, raw[successor],
                                         dest[ix], kinds[ix], arrival, rep_arrival))

targets = {}
for n in range(45, 50):
    key = f'rawClass_{n}'
    start = offsets[key]
    end = start + 16384
    first_code, last_code = start // 12, (end - 1) // 12
    codes = range(first_code, last_code + 1)
    valid = [code for code in codes if code in raw_codes]
    targets[key] = {
        'source_line': source[:source.index(f'private noncomputable def {key} ')].count('\n') + 1,
        'bit_offset': start,
        'bit_end_exclusive': end,
        'codes_touched': [first_code, last_code],
        'complete_lanes': [(start + 11) // 12, end // 12 - 1],
        'valid_codes_touched': len(valid),
        'invalid_codes_touched': len(codes) - len(valid),
        'coverage_errors': [err for err in coverage_errors if first_code <= err[0] <= last_code],
        'compatibility_errors': [err for err in compatibility_errors if first_code <= err[0] <= last_code],
        'first_valid_example': None if not valid else {
            'code': valid[0], 'word': ''.join(labels[d] for d in digits(valid[0])),
            'class': raw[valid[0]], 'representative_code': reps[raw[valid[0]]],
        },
    }

result = {
    'literal_count': len(literals),
    'raw_chunks': len(offsets),
    'counts_by_depth': [counts[i] for i in range(11)],
    'raw_class_range': [min(raw), max(raw)],
    'raw_valid_classes': len({raw[code] for code in raw_codes}),
    'coverage_errors_count': len(coverage_errors),
    'coverage_errors_first': coverage_errors[:10],
    'representative_errors_count': len(representative_errors),
    'representative_errors_first': representative_errors[:10],
    'row_errors_count': len(row_errors),
    'row_errors_first': row_errors[:10],
    'compatibility_errors_count': len(compatibility_errors),
    'compatibility_errors_first': compatibility_errors[:10],
    'all_direction_kind_errors_count': len(all_direction_kind_errors),
    'all_direction_kind_errors_first': all_direction_kind_errors[:10],
    'edge_kind_counts': dict(Counter(kinds[i] for i in range(4 * 3741) if dest[i] != 0)),
    'targets': targets,
}
out = Path(__file__).with_name('audit-results.json')
out.write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
