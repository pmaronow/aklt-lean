"""Independently check the paper's finite automaton contract against Lean literals.

Only reads the supplied Lean source. All generated artifacts stay in this directory.
This is an arithmetic/model check, not a Lean proof.
"""

import ast
import json
import re
from collections import Counter
from pathlib import Path


SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
HERE = Path(__file__).resolve().parent
text = SOURCE.read_text()
literals = {}
lines = {}
expressions = {}
for number, line in enumerate(text.splitlines(), 1):
    match = re.fullmatch(r'private noncomputable def (\w+) : ℕ := (0x[0-9a-f]+)', line)
    if match:
        literals[match[1]] = int(match[2], 16)
        lines[match[1]] = number
    match = re.fullmatch(r'noncomputable def (\w+) : ℕ := (.+)', line)
    if match:
        expressions[match[1]] = ast.parse(match[2].replace('<<<', '<<'), mode='eval').body


def evaluate(node):
    if isinstance(node, ast.Name):
        return literals[node.id]
    if isinstance(node, ast.Constant) and type(node.value) is int:
        return node.value
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add):
        return evaluate(node.left) + evaluate(node.right)
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.LShift):
        return evaluate(node.left) << evaluate(node.right)
    raise ValueError(ast.dump(node))


def positions(node, offset=0):
    if isinstance(node, ast.Name):
        return [(node.id, offset)]
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add):
        return positions(node.left, offset) + positions(node.right, offset)
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.LShift):
        return positions(node.left, offset + evaluate(node.right))
    raise ValueError(ast.dump(node))


class Table:
    def __init__(self, name, width):
        value = evaluate(expressions[name])
        self.bits = value.bit_length()
        self.data = value.to_bytes((self.bits + 7) // 8, 'little')
        self.width = width
        self.mask = (1 << width) - 1

    def __getitem__(self, index):
        bit = self.width * index
        byte, remainder = divmod(bit, 8)
        return (int.from_bytes(self.data[byte:byte + (remainder + self.width + 7) // 8], 'little') >> remainder) & self.mask


raw = Table('rawClass', 12)
representatives = Table('representatives', 20)
destinations = Table('destinations', 12)
kinds = Table('edgeKinds', 2)
offsets = dict(positions(expressions['rawClass']))
assert len(offsets) == 768
assert set(offsets) == {f'rawClass_{i}' for i in range(768)}

# Verify the actual concatenation, including its short final piece.
ordered = sorted(offsets.items(), key=lambda item: item[1])
raw_integer = int.from_bytes(raw.data, 'little')
for i, (name, offset) in enumerate(ordered):
    if i + 1 < len(ordered):
        assert literals[name].bit_length() <= ordered[i + 1][1] - offset
    assert (raw_integer >> offset) & ((1 << literals[name].bit_length()) - 1) == literals[name]

steps = ((1, 0), (0, 1), (-1, 0), (0, -1))


def bond(a, b):
    return tuple(sorted((a, b)))


def decode(code):
    return tuple((code >> (2 * i)) & 3 for i in range(9, -1, -1))


def geometry(word):
    vertices = [(0, 0)]
    bonds = set()
    for direction in word:
        dx, dy = steps[direction]
        x, y = vertices[-1]
        nxt = (x + dx, y + dy)
        edge = bond(vertices[-1], nxt)
        if edge in bonds:
            return None
        bonds.add(edge)
        vertices.append(nxt)
    return vertices, bonds


def row(word, geom):
    vertices, bonds = geom
    endpoint = vertices[-1]
    revisit = endpoint in vertices[:-1]
    result = []
    for d, (dx, dy) in enumerate(steps):
        target = (endpoint[0] + dx, endpoint[1] + dy)
        allowed = d != (word[-1] + 2) % 4 and bond(endpoint, target) not in bonds
        # The paper's kind definition is total, even on forbidden directions.
        kind = 2 if revisit else 0 if d == word[-1] else 1
        result.append((allowed, kind))
    return result


# Enumerate precisely all words with distinct unoriented bonds, without trusting
# the packed class map as an enumeration or imposing an incoming first bond.
windows = {}
counts = [0] * 11


def generate(word, code, vertices, bonds):
    counts[len(word)] += 1
    if len(word) == 10:
        windows[code] = (word, vertices, bonds)
        return
    x, y = vertices[-1]
    for direction, (dx, dy) in enumerate(steps):
        nxt = (x + dx, y + dy)
        edge = bond(vertices[-1], nxt)
        if edge not in bonds:
            generate(word + (direction,), code * 4 + direction,
                     vertices + [nxt], bonds | {edge})


generate((), 0, [(0, 0)], set())
errors = Counter()
examples = {}


def error(kind, value):
    errors[kind] += 1
    if kind not in examples:
        examples[kind] = value


for code in range(4**10):
    value = raw[code]
    if value > 3741:
        error('class_above_sentinel', [code, value])
    if (value < 3741) != (code in windows):
        error('raw_coverage', [code, value, code in windows])

representative_rows = []
for a in range(3741):
    code = representatives[a]
    if code >= 4**10 or code not in windows:
        error('representative_not_raw', [a, code])
        representative_rows.append(None)
        continue
    if raw[code] != a:
        error('representative_wrong_class', [a, code, raw[code]])
    word, vertices, bonds = windows[code]
    representative_rows.append(row(word, (vertices, bonds)))
    for d in range(4):
        dest, kind = destinations[a * 4 + d], kinds[a * 4 + d]
        if dest > 3741 or (dest == 0) != (kind == 3) or (dest != 0 and kind >= 3):
            error('stored_row_bounds', [a, d, dest, kind])

edge_counts = Counter()
for a in range(3741):
    for d in range(4):
        if destinations[a * 4 + d] != 0:
            edge_counts[kinds[a * 4 + d]] += 1

local_errors = {i: Counter() for i in range(750, 755)}
affected_codes = {}
for i in local_errors:
    name = f'rawClass_{i}'
    lo = offsets[name]
    hi = lo + 16384 - 1
    affected_codes[i] = set(range(lo // 12, hi // 12 + 1))

for code, (word, vertices, bonds) in windows.items():
    a = raw[code] % 3741  # exactly supplied.project
    actual_row = row(word, (vertices, bonds))
    rword = decode(representatives[a])
    for d, (allowed, kind) in enumerate(actual_row):
        destination, stored_kind = destinations[a * 4 + d], kinds[a * 4 + d]
        failures = []
        if allowed != (destination != 0):
            failures.append('admissibility')
        if representative_rows[a] is not None and kind != representative_rows[a][d][1]:
            failures.append('representative_kind_all_directions')
        if allowed:
            if kind != (0 if stored_kind == 0 else 1 if stored_kind == 1 else 2):
                failures.append('kind')
            successor_code = ((code % 4**9) * 4) + d
            expected_class = raw[successor_code] % 3741
            stored_class = max(destination - 1, 0) % 3741
            if expected_class != stored_class:
                failures.append('successor')
            if kind != 2 and word[-1] != rword[-1]:
                failures.append('arrival')
        for failure in failures:
            error(failure, {'code': code, 'word': word, 'class': a, 'direction': d,
                            'allowed': allowed, 'kind': kind,
                            'destination': destination, 'stored_kind': stored_kind,
                            'representative_code': representatives[a]})
            for i, codes in affected_codes.items():
                if code in codes:
                    local_errors[i][failure] += 1

details = []
for i, codes in affected_codes.items():
    name = f'rawClass_{i}'
    lo, hi = offsets[name], offsets[name] + 16384 - 1
    valid = sorted(codes & windows.keys())
    details.append({
        'name': name, 'line': lines[name], 'offset': lo, 'last_bit': hi,
        'literal_bits': literals[name].bit_length(),
        'first_code': min(codes), 'last_code': max(codes),
        'raw_count': len(valid), 'invalid_count': len(codes) - len(valid),
        'class_count': len({raw[c] for c in valid}),
        'local_errors': local_errors[i],
        'valid_boundary_samples': [[c, ''.join('ENWS'[d] for d in decode(c)), raw[c]]
                                   for c in (valid[:2] + valid[-2:])],
    })

result = {'literal_count': len(literals), 'raw_packed_bits': raw.bits,
          'counts_by_depth': counts, 'edge_counts': edge_counts,
          'errors': errors, 'first_examples': examples, 'declarations': details}
output = json.dumps(result, indent=2, sort_keys=True)
(HERE / 'check_results.json').write_text(output + '\n')
print(output)
