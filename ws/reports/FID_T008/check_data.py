"""Read-only reconstruction of the supplied Lean finite data and paper contract."""
from pathlib import Path
import ast
import re
from collections import Counter
import hashlib

SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
text = SOURCE.read_text()
literal_hex = dict(re.findall(r'private noncomputable def (\w+) : ℕ := 0x([0-9a-fA-F]+)', text))
literals = {name: int(h, 16) for name, h in literal_hex.items()}

def expression(name):
    line = re.search(r'^noncomputable def ' + name + r' : ℕ := (.+)$', text, re.M)[1]
    return ast.parse(line.replace('<<<', '<<'), mode='eval').body

def evaluate(node):
    if isinstance(node, ast.Name):
        return literals[node.id]
    if isinstance(node, ast.Constant):
        return node.value
    assert isinstance(node, ast.BinOp)
    lhs, rhs = evaluate(node.left), evaluate(node.right)
    if isinstance(node.op, ast.Add):
        return lhs + rhs
    assert isinstance(node.op, ast.LShift)
    return lhs << rhs

def offsets(node, shift=0):
    if isinstance(node, ast.Name):
        return [(node.id, shift)]
    assert isinstance(node, ast.BinOp)
    if isinstance(node.op, ast.Add):
        return offsets(node.left, shift) + offsets(node.right, shift)
    assert isinstance(node.op, ast.LShift)
    return offsets(node.left, shift + evaluate(node.right))

def unpack(name, width, count):
    value = evaluate(expression(name))
    data = value.to_bytes((width * count + 7) // 8, 'little')
    mask = (1 << width) - 1
    rows = []
    for i in range(count):
        bit = width * i
        start = bit // 8
        rows.append((int.from_bytes(data[start:start + 4], 'little') >> (bit % 8)) & mask)
    return rows

raw_offsets = dict(offsets(expression('rawClass')))
ordered_offsets = sorted(raw_offsets.items(), key=lambda pair: pair[1])
for (name, start), (_, stop) in zip(ordered_offsets, ordered_offsets[1:]):
    assert literals[name].bit_length() <= stop - start, (name, start, stop)
print('rawClass assembly:', len(raw_offsets), 'nonoverlapping chunks;',
      'bit length', evaluate(expression('rawClass')).bit_length())
raw = unpack('rawClass', 12, 4**10)
reps = unpack('representatives', 20, 3741)
dest = unpack('destinations', 12, 3741 * 4)
kinds = unpack('edgeKinds', 2, 3741 * 4)

steps = ((1, 0), (0, 1), (-1, 0), (0, -1))
def decode(code):
    return tuple((code >> (2 * (9 - i))) & 3 for i in range(10))

def geometry(word):
    vertices = [(0, 0)]
    bonds = []
    for d in word:
        x, y = vertices[-1]
        dx, dy = steps[d]
        v = (x + dx, y + dy)
        bonds.append(tuple(sorted((vertices[-1], v))))
        vertices.append(v)
    return vertices, bonds

def transitions(code):
    word = decode(code)
    vertices, bonds = geometry(word)
    x, y = vertices[-1]
    revisit = vertices[-1] in vertices[:-1]
    result = []
    for d, (dx, dy) in enumerate(steps):
        bond = tuple(sorted(((x, y), (x + dx, y + dy))))
        allowed = d != (word[-1] + 2) % 4 and bond not in bonds
        kind = 2 if revisit else (0 if d == word[-1] else 1)
        successor = (code % (4**9)) * 4 + d
        result.append((allowed, kind, successor))
    return word[-1], result

# Generate all raw windows independently by the exact distinct-bond recursion.
windows = []
counts = Counter()
def generate(code, vertex, used, depth):
    if depth:
        counts[depth] += 1
    if depth == 10:
        windows.append(code)
        return
    x, y = vertex
    for d, (dx, dy) in enumerate(steps):
        nxt = (x + dx, y + dy)
        bond = tuple(sorted((vertex, nxt)))
        if bond not in used:
            used.add(bond)
            generate(code * 4 + d, nxt, used, depth + 1)
            used.remove(bond)
generate(0, (0, 0), set(), 0)
window_set = set(windows)
print('Regenerated raw counts:', [counts[i] for i in range(1, 11)])
assert counts[10] == 60092

coverage_errors = [(code, a, code in window_set) for code, a in enumerate(raw)
                   if a > 3741 or (a < 3741) != (code in window_set)]
print('Coverage errors:', len(coverage_errors), coverage_errors[:10])
assert not coverage_errors
print('Representative errors:', sum(code not in window_set or raw[code] != a
                                    for a, code in enumerate(reps)))
assert all(code in window_set and raw[code] == a for a, code in enumerate(reps))
assert all(t <= 3741 and ((t == 0) == (k == 3)) for t, k in zip(dest, kinds))

edge_counts = Counter(k for t, k in zip(dest, kinds) if t != 0)
print('Quotient edge counts:', dict(sorted(edge_counts.items())))
assert edge_counts == {0: 2516, 1: 5032, 2: 1872}

errors = []
kind_errors_inadmissible = []
for code in windows:
    a = raw[code]
    arrival, row = transitions(code)
    rep_arrival, rep_row = transitions(reps[a])
    for d, (allowed, kind, successor) in enumerate(row):
        t, k = dest[a * 4 + d], kinds[a * 4 + d]
        if (t != 0) != allowed:
            errors.append((code, a, d, 'admissibility'))
        if kind != rep_row[d][1]:
            kind_errors_inadmissible.append((code, a, d))
        if allowed:
            if k != kind:
                errors.append((code, a, d, 'kind', k, kind))
            if t - 1 != raw[successor]:
                errors.append((code, a, d, 'successor', t - 1, raw[successor]))
            if kind != 2 and arrival != rep_arrival:
                errors.append((code, a, d, 'arrival'))
print('Raw/quotient transition errors:', len(errors), errors[:10])
print('All-directions representative-kind errors:', len(kind_errors_inadmissible),
      kind_errors_inadmissible[:10])
assert not errors

for i in range(5, 10):
    name = f'rawClass_{i}'
    offset = raw_offsets[name]
    width = next(stop for _, stop in ordered_offsets if stop > offset) - offset
    first, last = offset // 12, (offset + width - 1) // 12
    touched = list(range(first, last + 1))
    valid = [c for c in touched if c in window_set]
    print(name, 'line', 15 + 2 * i, 'offset', offset, 'width', width,
          'code interval', (first, last), 'valid', len(valid),
          'invalid', len(touched) - len(valid), 'class count', len({raw[c] for c in valid}),
          'bit offset within first lane', offset % 12,
          'end bit offset', (offset + width) % 12,
          'SHA256(hex)', hashlib.sha256(literal_hex[name].encode()).hexdigest())
    for c in valid[:2] + valid[-2:]:
        print('  example', c, ''.join('ENWS'[d] for d in decode(c)), 'class', raw[c],
              'representative', reps[raw[c]])

# Reconstruct the paper's sparse text archive from the decoded data.
lines = ['60092 3741']
lines += [f'{code} {raw[code]}' for code in windows]
for a, code in enumerate(reps):
    successor = [dest[a * 4 + d] - 1 for d in range(4)]
    kind = [kinds[a * 4 + d] if dest[a * 4 + d] else -1 for d in range(4)]
    lines.append(' '.join(map(str, [code] + successor + kind)))
archive = ('\n'.join(lines) + '\n').encode()
archive_hash = hashlib.sha256(archive).hexdigest()
print('Reconstructed sparse archive SHA256:', archive_hash)
claimed_hash = re.search(r'Archive SHA-256: ([0-9a-f]+)', text)[1]
print('Matches header hash:', archive_hash == claimed_hash)
