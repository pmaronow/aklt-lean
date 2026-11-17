"""Read-only reconstruction of the literal tables and paper automaton contract."""
from array import array
from collections import Counter
from pathlib import Path
import hashlib
import json
import re

SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
text = SOURCE.read_text()
values = {}
leaves = {}
locations = {}
literal_widths = {}


def parse(expr):
    tokens = re.findall(r'<<<|[()+]|[A-Za-z_]\w*|\d+', expr)
    assert ''.join(tokens) == re.sub(r'\s', '', expr)
    pos = 0

    def term():
        nonlocal pos
        t = tokens[pos]
        pos += 1
        if t == '(':
            result = expression()
            assert tokens[pos] == ')'
            pos += 1
            return result
        if t.isdigit():
            return int(t), []
        return values[t], list(leaves[t])

    def shift():
        nonlocal pos
        a, ls = term()
        while pos < len(tokens) and tokens[pos] == '<<<':
            pos += 1
            b, rs = term()
            assert not rs
            a <<= b
            ls = [(name, offset + b) for name, offset in ls]
        return a, ls

    def expression():
        nonlocal pos
        a, ls = shift()
        while pos < len(tokens) and tokens[pos] == '+':
            pos += 1
            b, rs = shift()
            a += b
            ls += rs
        return a, ls

    result = expression()
    assert pos == len(tokens)
    return result


for line_num, line in enumerate(text.splitlines(), 1):
    literal = re.fullmatch(r'private noncomputable def (\w+) : ℕ := 0x([0-9a-f]+)', line)
    composite = re.fullmatch(r'noncomputable def (\w+) : ℕ := (.*)', line)
    if literal:
        name, digits = literal.groups()
        values[name] = int(digits, 16)
        literal_widths[name] = 4 * len(digits)
        leaves[name] = [(name, 0)]
        locations[name] = line_num
    elif composite:
        name, expr = composite.groups()
        values[name], leaves[name] = parse(expr)

assert len(values) == 790  # 786 literal chunks and four composed tables.
expected_leaves = []
offset = 0
for i in reversed(range(768)):
    name = f'rawClass_{i}'
    expected_leaves.append((name, offset))
    offset += literal_widths[name]
assert leaves['rawClass'] == list(reversed(expected_leaves))
assert all(values[name] < 1 << 16384 for name, _ in leaves['rawClass'])
assert values['rawClass'].bit_length() <= 12 * 4**10


def lanes(packed, width, count):
    # Hex extraction avoids repeatedly shifting a twelve-million-bit integer.
    assert width % 4 == 0
    digits = width // 4
    h = f'{packed:0{digits * count}x}'
    assert len(h) == digits * count
    return array('H' if width <= 16 else 'I',
                 (int(h[j:j+digits], 16) for j in range(len(h)-digits, -1, -digits)))


classes = lanes(values['rawClass'], 12, 4**10)
reps = lanes(values['representatives'], 20, 3741)
dest = lanes(values['destinations'], 12, 3741 * 4)
kinds = [(values['edgeKinds'] >> (2 * i)) & 3 for i in range(3741 * 4)]
steps = [(1, 0), (0, 1), (-1, 0), (0, -1)]
counts = [0] * 11
raw = {}


def bond(x, y):
    return tuple(sorted((x, y)))


def generate(ds=(), vertices=((0, 0),), used=frozenset(), code=0):
    n = len(ds)
    counts[n] += 1
    if n == 10:
        raw[code] = (ds, vertices, used)
        return
    x = vertices[-1]
    for d, (dx, dy) in enumerate(steps):
        y = x[0] + dx, x[1] + dy
        b = bond(x, y)
        if b not in used:
            generate(ds + (d,), vertices + (y,), used | {b}, 4 * code + d)


generate()
assert counts == [1, 4, 12, 36, 108, 316, 916, 2628, 7500, 21268, 60092]
coverage_errors = [c for c, a in enumerate(classes) if a > 3741 or ((a < 3741) != (c in raw))]
assert not coverage_errors, coverage_errors[:10]
assert set(classes[c] for c in raw) == set(range(3741))
assert all(c in raw and classes[c] == a for a, c in enumerate(reps))
assert all(d <= 3741 and ((d == 0) == (k == 3)) for d, k in zip(dest, kinds))


def row(state):
    ds, vertices, used = state
    x = vertices[-1]
    revisit = x in vertices[:-1]
    ans = []
    for d, (dx, dy) in enumerate(steps):
        y = x[0] + dx, x[1] + dy
        allowed = d != (ds[-1] + 2) % 4 and bond(x, y) not in used
        kind = 2 if revisit else 0 if d == ds[-1] else 1
        ans.append((allowed, kind))
    return ans


row_errors = []
all_direction_kind_errors = []
for c, state in raw.items():
    a = classes[c]
    ds = state[0]
    rep_state = raw[reps[a]]
    rep_row = row(rep_state)
    for d, (allowed, kind) in enumerate(row(state)):
        i = a * 4 + d
        if kind != rep_row[d][1]:
            all_direction_kind_errors.append((c, a, d))
        if allowed != (dest[i] != 0) or allowed != rep_row[d][0]:
            row_errors.append((c, a, d, 'admissibility'))
        if allowed:
            successor = (c % (4**9)) * 4 + d
            assert successor in raw
            if kinds[i] != kind or kind != rep_row[d][1]:
                row_errors.append((c, a, d, 'kind'))
            if dest[i] - 1 != classes[successor]:
                row_errors.append((c, a, d, 'successor'))
            if kind != 2 and ds[-1] != rep_state[0][-1]:
                row_errors.append((c, a, d, 'arrival'))
assert not row_errors, row_errors[:10]
edge_counts = Counter(k for d, k in zip(dest, kinds) if d)
assert edge_counts == {0: 2516, 1: 5032, 2: 1872}

result = {
    'parsed_literal_chunks': 786,
    'raw_counts_by_length': counts,
    'coverage_errors': len(coverage_errors),
    'raw_words_checked': len(raw),
    'raw_direction_comparisons': 4 * len(raw),
    'quotient_classes': len(reps),
    'row_errors': len(row_errors),
    'all_direction_kind_errors': len(all_direction_kind_errors),
    'edge_counts_straight_turn_revisit': [edge_counts[i] for i in range(3)],
    'assigned': [],
}
for i in range(245, 250):
    name = f'rawClass_{i}'
    low = dict(leaves['rawClass'])[name]
    high = low + 16383
    first, last = low // 12, high // 12
    valid = [c for c in range(first, last + 1) if c in raw]
    result['assigned'].append({
        'name': name,
        'source_line': locations[name],
        'global_bit_range_inclusive': [low, high],
        'word_code_range_inclusive': [first, last],
        'boundary_lane_bit_offsets': [low % 12, (high + 1) % 12],
        'intersecting_lanes': last - first + 1,
        'raw_lanes': len(valid),
        'nonraw_lanes': last - first + 1 - len(valid),
        'distinct_classes': len({classes[c] for c in valid}),
        'first_raw_examples': [[c, classes[c]] for c in valid[:3]],
        'literal_sha256_big_endian_2048_bytes': hashlib.sha256(values[name].to_bytes(2048, 'big')).hexdigest(),
    })

# Attempt the simple text serialization specified by the paper, without reading
# the external archive. A matching digest would identify the exact archived data.
lines = ['60092 3741']
lines += [f'{c} {classes[c]}' for c in sorted(raw)]
for a, rep in enumerate(reps):
    ds = [dest[4*a+d] - 1 for d in range(4)]
    ks = [kinds[4*a+d] if dest[4*a+d] else -1 for d in range(4)]
    lines.append(' '.join(map(str, [rep] + ds + ks)))
result['reconstructed_archive_sha256'] = hashlib.sha256(('\n'.join(lines) + '\n').encode()).hexdigest()
result['matches_declared_archive_hash'] = result['reconstructed_archive_sha256'] == '671475d3333b646b3ace22a555f9a63a74f7bb076f0454f5b480c1e444a95785'
Path('check_results.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
