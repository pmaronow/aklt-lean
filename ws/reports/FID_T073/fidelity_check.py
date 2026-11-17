"""Independent finite reconstruction using only the supplied Lean literals."""

from collections import Counter
from hashlib import sha256
from pathlib import Path
import json
import re


SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
ASSIGNED = range(330, 335)
text = SOURCE.read_text()
values = {}
positions = {}
assemblies = {}
hex_data = {}


class Parser:
    def __init__(self, expression):
        self.tokens = re.findall(r'<<<|[()+]|\w+', expression)
        assert ''.join(self.tokens) == re.sub(r'\s+', '', expression)
        self.i = 0

    def atom(self):
        t = self.tokens[self.i]
        self.i += 1
        if t == '(':
            result = self.add()
            assert self.tokens[self.i] == ')'
            self.i += 1
            return result
        if t.isdecimal():
            return int(t), {}
        return values[t], {t: 0}

    def shift(self):
        value, leaves = self.atom()
        while self.i < len(self.tokens) and self.tokens[self.i] == '<<<':
            self.i += 1
            amount, no_leaves = self.atom()
            assert not no_leaves
            value <<= amount
            leaves = {k: v + amount for k, v in leaves.items()}
        return value, leaves

    def add(self):
        value, leaves = self.shift()
        while self.i < len(self.tokens) and self.tokens[self.i] == '+':
            self.i += 1
            other, more = self.shift()
            assert not (value & other), 'Packing addition has overlapping nonzero bits'
            assert not (leaves.keys() & more.keys()), 'Repeated chunk'
            value += other
            leaves.update(more)
        return value, leaves

    def parse(self):
        result = self.add()
        assert self.i == len(self.tokens)
        return result


for line_no, line in enumerate(text.splitlines(), 1):
    match = re.fullmatch(r'(?:private )?noncomputable def (\w+) : ℕ := (.+)', line)
    if not match:
        continue
    name, expression = match.groups()
    positions[name] = line_no
    if expression.startswith('0x'):
        assert re.fullmatch(r'0x[0-9a-f]+', expression)
        values[name] = int(expression, 16)
        hex_data[name] = expression[2:]
    else:
        values[name], assemblies[name] = Parser(expression).parse()

assert set(assemblies) == {'rawClass', 'representatives', 'destinations', 'edgeKinds'}
assert set(assemblies['rawClass']) == {f'rawClass_{i}' for i in range(768)}
for table, leaves in assemblies.items():
    previous_end = 0
    for name, offset in sorted(leaves.items(), key=lambda x: x[1]):
        assert offset == previous_end, (table, name, offset, previous_end)
        previous_end = offset + len(hex_data[name]) * 4
    assert values[table].bit_length() <= previous_end


def unpack(table, width, count):
    packed = values[table]
    b = packed.to_bytes((packed.bit_length() + 7) // 8, 'little')
    mask = (1 << width) - 1
    lanes = []
    for i in range(count):
        bit = i * width
        byte, shift = divmod(bit, 8)
        needed = (width + shift + 7) // 8
        lanes.append((int.from_bytes(b[byte:byte + needed], 'little') >> shift) & mask)
    assert not packed >> (width * count), 'Unexpected lanes beyond specified universe'
    return lanes


classes = unpack('rawClass', 12, 4 ** 10)
representatives = unpack('representatives', 20, 3741)
destinations = unpack('destinations', 12, 3741 * 4)
kinds = unpack('edgeKinds', 2, 3741 * 4)
steps = ((1, 0), (0, 1), (-1, 0), (0, -1))
raw = {}
depth_counts = Counter()


def generate(directions, vertices, bonds, code):
    n = len(directions)
    depth_counts[n] += 1
    if n == 10:
        raw[code] = (tuple(directions), tuple(vertices), frozenset(bonds))
        return
    x, y = vertices[-1]
    for d, (dx, dy) in enumerate(steps):
        new = (x + dx, y + dy)
        bond = tuple(sorted((vertices[-1], new)))
        if bond not in bonds:
            generate(directions + [d], vertices + [new], bonds | {bond}, 4 * code + d)


generate([], [(0, 0)], set(), 0)
assert dict(depth_counts) == dict(enumerate([1, 4, 12, 36, 108, 316, 916, 2628, 7500, 21268, 60092]))


def row(code):
    ds, vs, bonds = raw[code]
    arrival = ds[-1]
    revisit = vs[-1] in vs[:-1]
    x, y = vs[-1]
    result = []
    for d, (dx, dy) in enumerate(steps):
        bond = tuple(sorted((vs[-1], (x + dx, y + dy))))
        allowed = d != (arrival + 2) % 4 and bond not in bonds
        kind = 2 if revisit else (0 if d == arrival else 1)
        successor = (code % (4 ** 9)) * 4 + d
        result.append((allowed, kind, successor, arrival))
    return result


coverage_errors = []
representative_errors = []
row_errors = []
all_direction_kind_errors = []
for code, a in enumerate(classes):
    if a > 3741 or ((a < 3741) != (code in raw)):
        coverage_errors.append((code, a, code in raw))
for a, code in enumerate(representatives):
    if code not in raw or classes[code] != a:
        representative_errors.append((a, code, classes[code]))
for code in raw:
    a = classes[code]
    if a >= 3741:
        continue
    for d, (allowed, kind, successor, arrival) in enumerate(row(code)):
        edge = 4 * a + d
        stored_allowed = destinations[edge] != 0
        reasons = []
        if kind != row(representatives[a])[d][1]:
            all_direction_kind_errors.append((code, a, d))
        if stored_allowed != allowed:
            reasons.append('admissibility')
        if allowed:
            if kinds[edge] != kind:
                reasons.append('kind')
            if destinations[edge] != classes[successor] + 1:
                reasons.append('successor')
            if kind != 2 and representatives[a] % 4 != arrival:
                reasons.append('arrival')
        if reasons:
            row_errors.append((code, a, d, reasons))

destination_errors = [(i, dest, kinds[i]) for i, dest in enumerate(destinations)
                      if not (dest <= 3741 and ((dest == 0) == (kinds[i] == 3))
                              and (dest == 0 or kinds[i] < 3))]
edge_counts = Counter(kinds[i] for i, dest in enumerate(destinations) if dest)

# Reconstruct the simple integer-row archive format described by the paper.
archive_rows = ['60092 3741']
archive_rows.extend(f'{code} {classes[code]}' for code in sorted(raw))
for a, code in enumerate(representatives):
    ds = [destinations[4 * a + d] - 1 for d in range(4)]
    ks = [-1 if kinds[4 * a + d] == 3 else kinds[4 * a + d] for d in range(4)]
    archive_rows.append(' '.join(map(str, [code] + ds + ks)))
reconstructed_sha256 = sha256(('\n'.join(archive_rows) + '\n').encode()).hexdigest()
declared_sha256 = re.search(r'Archive SHA-256: ([0-9a-f]{64})', text)[1]

# Check the arithmetic most-significant-first coding against the DFS encoding.
coding_errors = []
for code, (ds, vs, bonds) in raw.items():
    decoded = tuple((code // 4 ** (9 - i)) % 4 for i in range(10))
    encoded = sum(d * 4 ** (9 - i) for i, d in enumerate(ds))
    if decoded != ds or encoded != code:
        coding_errors.append(code)

chunk_info = []
for i in ASSIGNED:
    name = f'rawClass_{i}'
    offset = assemblies['rawClass'][name]
    width = 4 * len(hex_data[name])
    low_code, high_code = offset // 12, (offset + width - 1) // 12
    affected = range(low_code, high_code + 1)
    relevant = [code for code in affected if code in raw]
    chunk_info.append(dict(
        name=name, line=positions[name], hex_digits=len(hex_data[name]),
        sha256_hex=sha256(hex_data[name].encode()).hexdigest(),
        bit_interval=[offset, offset + width - 1],
        intersecting_codes=[low_code, high_code],
        raw_codes=len(relevant), invalid_codes=len(affected) - len(relevant),
        distinct_classes=len({classes[code] for code in relevant}),
        coverage_errors=[x for x in coverage_errors if low_code <= x[0] <= high_code],
        row_errors=[x for x in row_errors if low_code <= x[0] <= high_code],
        first_raw_examples=[(c, classes[c], ''.join('ENWS'[d] for d in raw[c][0])) for c in relevant[:3]],
    ))

result = dict(
    parsed_literal_chunks=len(hex_data), all_packing_ranges_contiguous=True,
    raw_class_bits=values['rawClass'].bit_length(),
    depth_counts=dict(depth_counts), coverage_error_count=len(coverage_errors),
    representative_error_count=len(representative_errors),
    row_error_count=len(row_errors), destination_error_count=len(destination_errors),
    all_direction_kind_error_count=len(all_direction_kind_errors),
    coding_error_count=len(coding_errors),
    reconstructed_archive_sha256=reconstructed_sha256,
    declared_archive_sha256=declared_sha256,
    archive_hash_matches=reconstructed_sha256 == declared_sha256,
    edge_counts=dict(edge_counts), chunks=chunk_info,
    first_coverage_errors=coverage_errors[:8],
    first_representative_errors=representative_errors[:8],
    first_row_errors=row_errors[:8],
)
print(json.dumps(result, indent=2))
Path('check_results.json').write_text(json.dumps(result, indent=2) + '\n')

assert not coverage_errors
assert not representative_errors
assert not row_errors
assert not all_direction_kind_errors
assert not coding_errors
assert not destination_errors
assert edge_counts == {0: 2516, 1: 5032, 2: 1872}
