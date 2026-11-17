"""Read-only reconstruction of the paper's automaton contract from Lean literals."""
from pathlib import Path
import collections
import hashlib
import json
import re

SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
text = SOURCE.read_text()
lines = text.splitlines()
literals = {
    name: int(value, 16)
    for name, value in re.findall(
        r'^private noncomputable def (\w+) : ℕ := (0x[0-9a-fA-F]+)$', text, re.M
    )
}


def parse_assembly(name):
    expr = re.search(r'^noncomputable def ' + name + r' : ℕ := (.+)$', text, re.M)[1]
    tokens = re.findall(r'\w+|<<<|[()+]', expr)
    assert ''.join(tokens) == re.sub(r'\s+', '', expr)
    cursor = 0

    def atom():
        nonlocal cursor
        tok = tokens[cursor]
        cursor += 1
        if tok == '(':
            result = expression()
            assert tokens[cursor] == ')'
            cursor += 1
            return result
        assert tok in literals
        return [(tok, 0)]

    def expression():
        nonlocal cursor
        result = atom()
        while cursor < len(tokens) and tokens[cursor] != ')':
            op = tokens[cursor]
            cursor += 1
            if op == '<<<':
                amount = int(tokens[cursor])
                cursor += 1
                result = [(n, offset + amount) for n, offset in result]
            else:
                assert op == '+'
                result += atom()
        return result

    terms = expression()
    assert cursor == len(tokens)
    assert len({n for n, _ in terms}) == len(terms)
    ordered = sorted(terms, key=lambda t: t[1])
    assert ordered[0][1] == 0
    for (n, offset), (_, next_offset) in zip(ordered, ordered[1:]):
        assert literals[n].bit_length() <= next_offset - offset
    value = sum(literals[n] << offset for n, offset in terms)
    return value.to_bytes((value.bit_length() + 7) // 8, 'little'), dict(terms)


tables = {}
offsets = {}
for name in ['rawClass', 'representatives', 'destinations', 'edgeKinds']:
    tables[name], offsets[name] = parse_assembly(name)


def lane(name, width, index):
    bit = width * index
    byte, intra = divmod(bit, 8)
    size = (intra + width + 7) // 8
    return (int.from_bytes(tables[name][byte:byte + size], 'little') >> intra) & ((1 << width) - 1)


classes = [lane('rawClass', 12, code) for code in range(4**10)]
reps = [lane('representatives', 20, a) for a in range(3741)]
dest = [[lane('destinations', 12, 4*a+d) for d in range(4)] for a in range(3741)]
kinds = [[lane('edgeKinds', 2, 4*a+d) for d in range(4)] for a in range(3741)]
steps = [(1, 0), (0, 1), (-1, 0), (0, -1)]
raw = {}
counts = [0] * 11


def bond(x, y):
    return tuple(sorted((x, y)))


def generate(code, directions, vertices, used):
    depth = len(directions)
    counts[depth] += 1
    x = vertices[-1]
    if depth == 10:
        revisit = x in vertices[:-1]
        allowed = []
        rowkind = []
        for d, (dx, dy) in enumerate(steps):
            y = (x[0] + dx, x[1] + dy)
            allowed.append(d != (directions[-1] + 2) % 4 and bond(x, y) not in used)
            rowkind.append(2 if revisit else (0 if d == directions[-1] else 1))
        raw[code] = (allowed, rowkind, directions[-1])
        return
    for d, (dx, dy) in enumerate(steps):
        y = (x[0] + dx, x[1] + dy)
        edge = bond(x, y)
        if edge not in used:
            used.add(edge)
            directions.append(d)
            vertices.append(y)
            generate(code*4+d, directions, vertices, used)
            vertices.pop()
            directions.pop()
            used.remove(edge)


generate(0, [], [(0, 0)], set())
errors = collections.Counter()
examples = {}


def check(ok, label, detail):
    if not ok:
        errors[label] += 1
        examples.setdefault(label, detail)


for code, a in enumerate(classes):
    check(a <= 3741, 'class_range', [code, a])
    check((a < 3741) == (code in raw), 'raw_coverage', [code, a])
for a, rep in enumerate(reps):
    check(rep < 4**10, 'rep_range', [a, rep])
    check(rep in raw, 'rep_raw', [a, rep])
    check(classes[rep] == a, 'rep_section', [a, rep, classes[rep]])
    for d in range(4):
        check(dest[a][d] <= 3741, 'destination_range', [a, d])
        check((dest[a][d] == 0) == (kinds[a][d] == 3), 'edge_sentinel', [a, d])

for code, (allowed, rowkind, arrival) in raw.items():
    a = classes[code]
    if not 0 <= a < 3741:
        continue
    representative = raw.get(reps[a])
    if representative:
        check(allowed == representative[0], 'representative_admissibility', [code, a])
        check(rowkind == representative[1], 'representative_kind_all_directions', [code, a])
    for d in range(4):
        check((dest[a][d] != 0) == allowed[d], 'stored_admissibility', [code, a, d])
        if allowed[d]:
            check(kinds[a][d] == rowkind[d], 'stored_kind', [code, a, d])
            successor = (code % (4**9))*4+d
            check(successor in raw, 'successor_raw', [code, d, successor])
            check(dest[a][d] == classes[successor]+1, 'stored_successor', [code, a, d])
            if rowkind[d] != 2:
                check(reps[a] % 4 == arrival, 'nonrevisit_arrival', [code, a, d])

edgecounts = collections.Counter(kinds[a][d] for a in range(3741) for d in range(4) if dest[a][d])
chunks = []
for i in range(525, 530):
    name = f'rawClass_{i}'
    start = offsets['rawClass'][name]
    end = start + 16384
    # Every target is a full 16384-bit slot, including any leading zeros.
    assert offsets['rawClass'][f'rawClass_{i-1}'] == end
    touched = range(start // 12, (end + 11) // 12)
    full = range((start + 11) // 12, end // 12)
    selected_raw = [c for c in touched if c in raw]
    chunks.append({
        'name': name,
        'source_line': next(n for n, line in enumerate(lines, 1) if f'def {name} :' in line),
        'bit_start_inclusive': start,
        'bit_end_exclusive': end,
        'touched_codes_inclusive': [touched.start, touched.stop-1],
        'complete_lanes_inclusive': [full.start, full.stop-1],
        'raw_codes_touched': len(selected_raw),
        'invalid_codes_touched': len(touched)-len(selected_raw),
        'boundary_lanes': [[c, classes[c]] for c in (touched.start, touched.stop-1)],
        'first_raw_examples': [[c, classes[c]] for c in selected_raw[:3]],
        'last_raw_examples': [[c, classes[c]] for c in selected_raw[-3:]],
        'sha256_2048_little_endian_bytes': hashlib.sha256(literals[name].to_bytes(2048, 'little')).hexdigest(),
    })

result = {
    'input': str(SOURCE),
    'raw_generation_counts_depth_0_to_10': counts,
    'range_raw_coverage_and_quotient_errors': dict(errors),
    'first_error_examples': examples,
    'class_count': len(set(classes[c] for c in raw)),
    'edge_counts_straight_turn_revisit': [edgecounts[k] for k in range(3)],
    'raw_class_literal_count': len(offsets['rawClass']),
    'raw_assembly_chunk_reference_order_is_0_through_767': list(offsets['rawClass']) == [f'rawClass_{i}' for i in range(768)],
    'chunks': chunks,
}
print(json.dumps(result, indent=2))
Path('check_results.json').write_text(json.dumps(result, indent=2) + '\n')
assert not errors
assert counts[1:] == [4,12,36,108,316,916,2628,7500,21268,60092]
assert len(set(classes[c] for c in raw)) == 3741
assert [edgecounts[k] for k in range(3)] == [2516,5032,1872]
