"""Read-only reconstruction of the supplied Lean automaton literal tables."""

from collections import Counter
from pathlib import Path
import hashlib
import json
import re

SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
TEXT = SOURCE.read_text()
LITERALS = {
    name: int(digits, 16)
    for name, digits in re.findall(
        r'^private noncomputable def (\w+) : ℕ := 0x([0-9a-f]+)$', TEXT, re.M
    )
}


def parse(expression):
    tokens = re.findall(r'\w+|<<<|[()+]', expression)
    assert ''.join(tokens) == re.sub(r'\s', '', expression)
    position = 0

    def atom():
        nonlocal position
        token = tokens[position]
        position += 1
        if token == '(':
            node = expr()
            assert tokens[position] == ')'
            position += 1
            return node
        return int(token) if token.isdigit() else token

    def expr():
        nonlocal position
        left = atom()
        while position < len(tokens) and tokens[position] in ('+', '<<<'):
            op = tokens[position]
            position += 1
            left = (op, left, atom())
        return left

    tree = expr()
    assert position == len(tokens)
    return tree


def flatten(node, offset=0):
    if isinstance(node, str):
        return [(node, offset)]
    op, left, right = node
    if op == '<<<':
        assert isinstance(right, int)
        return flatten(left, offset + right)
    return flatten(left, offset) + flatten(right, offset)


def unpack(name, width, length):
    expression = re.search(
        r'^noncomputable def ' + name + r' : ℕ := (.+)$', TEXT, re.M
    ).group(1)
    pieces = flatten(parse(expression))
    assert len({key for key, _ in pieces}) == len(pieces)
    assert set(key for key, _ in pieces) == {
        key for key in LITERALS if key.startswith(name + '_')
    }
    ordered = sorted(pieces, key=lambda pair: pair[1])
    for (key, offset), (_, next_offset) in zip(ordered, ordered[1:]):
        assert LITERALS[key] < 1 << (next_offset - offset), key
    packed = sum(LITERALS[key] << offset for key, offset in pieces)
    assert packed.bit_length() <= width * length
    # Read once through bytes rather than repeatedly shifting a 12-million-bit integer.
    data = packed.to_bytes((width * length + 7) // 8, 'little')
    mask = (1 << width) - 1
    lanes = []
    for index in range(length):
        bit = width * index
        start, remainder = divmod(bit, 8)
        count = (remainder + width + 7) // 8
        lanes.append((int.from_bytes(data[start:start + count], 'little') >> remainder) & mask)
    return lanes, dict(pieces), data


RAW, OFFSETS, RAW_BYTES = unpack('rawClass', 12, 4**10)
REPS, _, _ = unpack('representatives', 20, 3741)
DEST, _, _ = unpack('destinations', 12, 3741 * 4)
KINDS, _, _ = unpack('edgeKinds', 2, 3741 * 4)

STEPS = ((1, 0), (0, 1), (-1, 0), (0, -1))


def bond(x, y):
    return (x, y) if x < y else (y, x)


def geometry(code):
    directions = [(code >> (2 * (9 - i))) & 3 for i in range(10)]
    point = (0, 0)
    vertices = [point]
    bonds = []
    for d in directions:
        dx, dy = STEPS[d]
        nxt = (point[0] + dx, point[1] + dy)
        bonds.append(bond(point, nxt))
        point = nxt
        vertices.append(point)
    return directions, vertices, bonds


counts = [0] * 11
windows = []


def generate(depth, code, point, used):
    counts[depth] += 1
    if depth == 10:
        windows.append(code)
        return
    for d, (dx, dy) in enumerate(STEPS):
        nxt = (point[0] + dx, point[1] + dy)
        edge = bond(point, nxt)
        if edge not in used:
            used.add(edge)
            generate(depth + 1, code * 4 + d, nxt, used)
            used.remove(edge)


generate(0, 0, (0, 0), set())
assert counts == [1, 4, 12, 36, 108, 316, 916, 2628, 7500, 21268, 60092]
assert windows == sorted(set(windows))
raw_set = set(windows)
assert min(RAW) == 0 and max(RAW) == 3741
assert {i for i, a in enumerate(RAW) if a < 3741} == raw_set
assert {RAW[code] for code in windows} == set(range(3741))
assert all(code in raw_set and RAW[code] == a for a, code in enumerate(REPS))
assert len(set(REPS)) == 3741
assert all(0 <= d <= 3741 for d in DEST)
assert all((d == 0) == (k == 3) for d, k in zip(DEST, KINDS))

admitted = 0
raw_edge_kinds = Counter()
representative_geometry = [geometry(code) for code in REPS]
for code in windows:
    a = RAW[code]
    directions, vertices, bonds = geometry(code)
    used = set(bonds)
    assert len(used) == 10
    point = vertices[-1]
    revisit = point in vertices[:-1]
    rep_directions, rep_vertices, _ = representative_geometry[a]
    rep_revisit = rep_vertices[-1] in rep_vertices[:-1]
    for d, (dx, dy) in enumerate(STEPS):
        kind = 2 if revisit else (0 if d == directions[-1] else 1)
        rep_kind = 2 if rep_revisit else (0 if d == rep_directions[-1] else 1)
        assert kind == rep_kind, (code, a, d, 'all-direction kind compatibility')
        nxt = (point[0] + dx, point[1] + dy)
        allowed = d != (directions[-1] + 2) % 4 and bond(point, nxt) not in used
        row_index = a * 4 + d
        assert allowed == (DEST[row_index] != 0), (code, a, d, 'admissibility')
        if allowed:
            assert KINDS[row_index] == kind, (code, a, d, 'kind')
            successor_code = (code % 4**9) * 4 + d
            assert successor_code in raw_set
            assert RAW[successor_code] == DEST[row_index] - 1, (code, a, d, 'successor')
            if kind != 2:
                assert REPS[a] % 4 == directions[-1], (code, a, d, 'arrival')
            admitted += 1
            raw_edge_kinds[kind] += 1

edge_counts = Counter(k for d, k in zip(DEST, KINDS) if d != 0)
assert edge_counts == {0: 2516, 1: 5032, 2: 1872}

# Rebuild the paper's text format from the tables, undoing the two sentinels.
archive_lines = ['60092 3741']
archive_lines.extend(f'{code} {RAW[code]}' for code in windows)
for a, rep in enumerate(REPS):
    destinations = DEST[a * 4:a * 4 + 4]
    kinds = KINDS[a * 4:a * 4 + 4]
    row = [rep] + [d - 1 for d in destinations] + [k if k < 3 else -1 for k in kinds]
    archive_lines.append(' '.join(map(str, row)))
archive_hash = hashlib.sha256(('\n'.join(archive_lines) + '\n').encode()).hexdigest()
declared_hash = re.search(r'Archive SHA-256: ([0-9a-f]{64})', TEXT).group(1)
assert archive_hash == declared_hash

target_results = []
for index in range(5):
    name = f'rawClass_{index}'
    offset = OFFSETS[name]
    assert LITERALS[name].bit_length() <= 16384
    high = offset + 16384
    first, last = offset // 12, (high - 1) // 12
    complete_first, complete_end = (offset + 11) // 12, high // 12
    complete = list(range(complete_first, complete_end))
    valid = [code for code in complete if code in raw_set]
    touching = list(range(first, last + 1))
    target_results.append({
        'name': name,
        'source_line': 15 + 2 * index,
        'bit_offset': offset,
        'bit_end_exclusive': high,
        'offset_mod_12': offset % 12,
        'complete_code_first': complete_first,
        'complete_code_last': complete_end - 1,
        'complete_codes': len(complete),
        'complete_valid': len(valid),
        'complete_invalid': len(complete) - len(valid),
        'touching_code_first': first,
        'touching_code_last': last,
        'touching_valid': sum(code in raw_set for code in touching),
        'example_valid': [(code, RAW[code]) for code in valid[:3]],
        'sha256_big_endian_2048_bytes': hashlib.sha256(LITERALS[name].to_bytes(2048, 'big')).hexdigest(),
    })

result = {
    'source_sha256': hashlib.sha256(TEXT.encode()).hexdigest(),
    'raw_packed_sha256_little_endian': hashlib.sha256(RAW_BYTES).hexdigest(),
    'reconstructed_archive_sha256': archive_hash,
    'archive_hash_matches_declared': True,
    'raw_window_counts': counts,
    'valid_codes': len(windows),
    'invalid_codes': len(RAW) - len(windows),
    'classes': 3741,
    'raw_admissible_edges': admitted,
    'raw_edge_kinds': dict(raw_edge_kinds),
    'quotient_edge_kinds': dict(edge_counts),
    'target_chunks': target_results,
}
Path('check_results.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
