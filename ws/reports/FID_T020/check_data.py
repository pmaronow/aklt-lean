"""Independent integer reconstruction of the supplied Lean data and paper checks.
Reads only the permitted Lean source. No Lean process or input mutation.
"""
from pathlib import Path
import ast
import collections
import hashlib
import json
import re

ROOT = Path('/home/ubuntu/aklt/reports/FID_T020')
SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
s = SOURCE.read_text()
literals = dict(re.findall(r'^private noncomputable def (\w+) : ℕ := 0x([0-9a-f]+)$', s, re.M))


def terms(node, offset=0):
    if isinstance(node, ast.Name):
        return [(node.id, offset)]
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add):
        return terms(node.left, offset) + terms(node.right, offset)
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.LShift):
        return terms(node.left, offset + ast.literal_eval(node.right))
    raise ValueError(ast.dump(node))


def unpack(name, width, count):
    expr = re.search(r'^noncomputable def ' + name + r' : ℕ := (.*)$', s, re.M)[1]
    pieces = sorted(terms(ast.parse(expr.replace('<<<', '<<'), mode='eval').body), key=lambda t: t[1])
    assert len({n for n, _ in pieces}) == len(pieces)
    packed = 0
    previous_end = 0
    for n, offset in pieces:
        value = int(literals[n], 16)
        assert offset >= previous_end, (n, offset, previous_end)
        packed += value << offset
        previous_end = offset + value.bit_length()
    assert packed.bit_length() <= width * count
    buf = packed.to_bytes((width * count + 7) // 8, 'little')
    mask = (1 << width) - 1
    lanes = []
    for code in range(count):
        bit = width * code
        byte, shift = divmod(bit, 8)
        size = (width + shift + 7) // 8
        lanes.append((int.from_bytes(buf[byte:byte + size], 'little') >> shift) & mask)
    return lanes, dict(pieces)


classes, offsets = unpack('rawClass', 12, 4**10)
representatives, _ = unpack('representatives', 20, 3741)
destinations, _ = unpack('destinations', 12, 3741 * 4)
kinds, _ = unpack('edgeKinds', 2, 3741 * 4)
assert [(f'rawClass_{767-j}', offsets[f'rawClass_{767-j}']) for j in range(768)] == [
    (f'rawClass_{767-j}', 0 if j == 0 else 16384*j - 4) for j in range(768)]

# E,N,W,S and most-significant-first codes. Bonds have unordered endpoints.
steps = ((1, 0), (0, 1), (-1, 0), (0, -1))
counts = [0] * 11
raw = {}


def bond(a, b):
    return tuple(sorted((a, b)))


def visit(depth, code, endpoint, used, departures, last):
    counts[depth] += 1
    if depth == 10:
        raw[code] = (endpoint, frozenset(used), frozenset(departures), last)
        return
    for d, (dx, dy) in enumerate(steps):
        target = (endpoint[0] + dx, endpoint[1] + dy)
        edge = bond(endpoint, target)
        if edge not in used:
            visit(depth + 1, 4 * code + d, target, used | {edge}, departures | {endpoint}, d)


visit(0, 0, (0, 0), set(), set(), None)
assert counts == [1, 4, 12, 36, 108, 316, 916, 2628, 7500, 21268, 60092]
assert len(raw) == 60092
assert set(c for c, a in enumerate(classes) if a < 3741) == set(raw)
assert max(classes) == 3741
assert set(classes[c] for c in raw) == set(range(3741))
assert len(set(representatives)) == 3741
assert all(c in raw and classes[c] == a for a, c in enumerate(representatives))
assert all(0 <= c < 4**10 for c in representatives)
assert all(0 <= dest <= 3741 for dest in destinations)
assert all((dest == 0) == (kind == 3) for dest, kind in zip(destinations, kinds))


def regenerated(code, d):
    endpoint, used, departures, last = raw[code]
    dx, dy = steps[d]
    target = (endpoint[0] + dx, endpoint[1] + dy)
    allowed = d != (last + 2) % 4 and bond(endpoint, target) not in used
    kind = 2 if endpoint in departures else (0 if d == last else 1)
    successor_code = (code % 4**9) * 4 + d
    if allowed:
        assert successor_code in raw
    return allowed, kind, successor_code, last


# All representative rows, retaining four labelled directions separately.
for a, code in enumerate(representatives):
    for d in range(4):
        allowed, kind, successor, last = regenerated(code, d)
        index = a * 4 + d
        assert (destinations[index] != 0) == allowed, (a, d, 'allowed')
        if allowed:
            assert kinds[index] == kind, (a, d, 'kind')
            assert destinations[index] - 1 == classes[successor], (a, d, 'successor')

# Check the full paper quotient contract on every raw word, including kinds
# on inadmissible directions and arrival directions on non-revisit edges.
for code in raw:
    a = classes[code]
    for d in range(4):
        allowed, kind, successor, last = regenerated(code, d)
        rep_allowed, rep_kind, _, rep_last = regenerated(representatives[a], d)
        assert allowed == rep_allowed, (code, a, d, 'allowed')
        assert kind == rep_kind, (code, a, d, 'all-direction kind')
        if allowed:
            assert kinds[4*a+d] == kind, (code, a, d, 'stored kind')
            assert destinations[4*a+d] - 1 == classes[successor], (code, a, d, 'successor')
            if kind != 2:
                assert last == rep_last, (code, a, d, 'arrival')

edge_counts = [sum(dest != 0 and kind == k for dest, kind in zip(destinations, kinds)) for k in range(3)]
assert edge_counts == [2516, 5032, 1872]

# Recreate the specified text rows as an additional, reproducible identity check.
archive_lines = ['60092 3741']
archive_lines += [f'{code} {classes[code]}' for code in sorted(raw)]
for a, representative in enumerate(representatives):
    successors = [destinations[4*a+d] - 1 for d in range(4)]
    row_kinds = [kinds[4*a+d] if destinations[4*a+d] else -1 for d in range(4)]
    archive_lines.append(' '.join(map(str, [representative] + successors + row_kinds)))
archive = ('\n'.join(archive_lines) + '\n').encode()
archive_sha = hashlib.sha256(archive).hexdigest()
declared_sha = re.search(r'Archive SHA-256: ([0-9a-f]{64})', s)[1]

results = {
    'raw_counts_by_depth': counts,
    'raw_class_histogram': {'raw': len(raw), 'invalid': len(classes)-len(raw), 'max': max(classes)},
    'representative_checks': 3741,
    'raw_direction_checks': len(raw)*4,
    'edge_counts_straight_turn_revisit': edge_counts,
    'reconstructed_archive_sha256': archive_sha,
    'declared_archive_sha256': declared_sha,
    'reconstructed_archive_matches_declared_sha256': archive_sha == declared_sha,
    'declarations': {},
}
for i in range(65, 70):
    name = f'rawClass_{i}'
    offset = offsets[name]
    first, last = offset // 12, (offset + 16384 - 1) // 12
    valid = [code for code in range(first, last+1) if code in raw]
    line = next(n for n, text in enumerate(s.splitlines(), 1) if text.startswith('private noncomputable def '+name+' '))
    results['declarations'][name] = {
        'lean_line': line,
        'hex_digits': len(literals[name]),
        'bit_length': int(literals[name], 16).bit_length(),
        'shift_in_rawClass': offset,
        'first_overlapping_word_code': first,
        'last_overlapping_word_code': last,
        'first_lane_bit_offset_in_chunk': 12*first-offset,
        'last_lane_bits_in_chunk': offset+16384-12*last,
        'overlapping_lanes': last-first+1,
        'raw_lanes': len(valid),
        'invalid_lanes': last-first+1-len(valid),
        'distinct_raw_classes': len({classes[c] for c in valid}),
        'literal_hex_sha256': hashlib.sha256(literals[name].encode()).hexdigest(),
        'first_raw_examples': [{'code': c, 'class': classes[c], 'representative': representatives[classes[c]]} for c in valid[:3]],
    }
(ROOT / 'check_results.json').write_text(json.dumps(results, indent=2) + '\n')
print(json.dumps(results, indent=2))
