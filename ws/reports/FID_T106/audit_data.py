"""Read-only reconstruction of the assigned Lean literal data and paper contract."""

from collections import Counter
import hashlib
import json
from pathlib import Path
import re


SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
TEXT = SOURCE.read_text()
LITERALS = {}
LINES = {}
for line_number, line in enumerate(TEXT.splitlines(), 1):
    match = re.fullmatch(r'private noncomputable def (\w+) : ℕ := (0x[0-9a-f]+)', line)
    if match:
        LITERALS[match[1]] = int(match[2], 16)
        LINES[match[1]] = line_number


def unpack_family(family, width, count):
    line = next(line for line in TEXT.splitlines()
                if line.startswith('noncomputable def ' + family + ' :'))
    expression = line.split(' := ', 1)[1]
    tokens = re.findall(r'\w+|<<<|[()+]', expression)
    assert ''.join(tokens) == re.sub(r'\s', '', expression)
    position = 0

    def atom():
        nonlocal position
        token = tokens[position]
        position += 1
        if token == '(':
            value = parse()
            assert tokens[position] == ')'
            position += 1
            return value
        return token

    def parse():
        nonlocal position
        value = atom()
        # All arithmetic nodes in these generated expressions are explicitly
        # parenthesized: no dependence on the precedence of <<< versus +.
        if position < len(tokens) and tokens[position] in ('+', '<<<'):
            operator = tokens[position]
            position += 1
            value = (operator, value, atom())
            assert position == len(tokens) or tokens[position] == ')'
        return value

    tree = parse()
    assert position == len(tokens)
    offsets = {}

    def collect(node, offset=0):
        if isinstance(node, str):
            assert node.startswith(family + '_') and node not in offsets
            offsets[node] = offset
            return LITERALS[node] << offset
        if node[0] == '+':
            return collect(node[1], offset) + collect(node[2], offset)
        assert isinstance(node[2], str) and node[2].isdigit()
        return collect(node[1], offset + int(node[2]))

    packed = collect(tree)
    names = sorted(offsets, key=offsets.get)
    for lower, upper in zip(names, names[1:]):
        assert LITERALS[lower].bit_length() <= offsets[upper] - offsets[lower]
    assert packed < 1 << (width * count)
    data = packed.to_bytes((width * count + 7) // 8, 'little')
    mask = (1 << width) - 1
    values = []
    for index in range(count):
        bit = width * index
        start = bit // 8
        value = int.from_bytes(data[start:start + (width + 14) // 8], 'little')
        values.append((value >> (bit % 8)) & mask)
    return values, offsets


raw, offsets = unpack_family('rawClass', 12, 4 ** 10)
representatives, _ = unpack_family('representatives', 20, 3741)
destinations, _ = unpack_family('destinations', 12, 3741 * 4)
kinds, _ = unpack_family('edgeKinds', 2, 3741 * 4)
assert len(LITERALS) == 768 + 5 + 11 + 2
assert set(raw) == set(range(3742))
assert max(representatives) < 4 ** 10
assert max(destinations) <= 3741
assert all((destination == 0) == (kind == 3)
           for destination, kind in zip(destinations, kinds))
assert all(raw[code] == cls for cls, code in enumerate(representatives))

steps = ((1, 0), (0, 1), (-1, 0), (0, -1))


def representative_kinds(code):
    directions = [(code // (4 ** power)) % 4 for power in range(9, -1, -1)]
    points = [(0, 0)]
    for direction in directions:
        x, y = points[-1]
        dx, dy = steps[direction]
        points.append((x + dx, y + dy))
    revisit = points[-1] in points[:-1]
    return [2 if revisit else (0 if direction == directions[-1] else 1)
            for direction in range(4)]


representative_raw_kinds = [representative_kinds(code) for code in representatives]
counts = [0] * 11
raw_codes = []
raw_code_set = set()
errors = Counter()
examples = {}
vertices = [(0, 0)]
word = []
bonds = set()
visits = Counter({(0, 0): 1})
checked_edges = 0
chunk_stats = {}
for number in range(495, 500):
    name = f'rawClass_{number}'
    offset = offsets[name]
    chunk_stats[name] = {
        'lean_line': LINES[name],
        'offset_bits': offset,
        'width_bits': 16384,
        'first_affected_code': offset // 12,
        'last_affected_code': (offset + 16383) // 12,
        'raw_words': 0,
        'invalid_words': 0,
        'checked_admissible_edges': 0,
        'classes': set(),
        'examples': [],
    }


def check(condition, key, detail):
    if not condition:
        errors[key] += 1
        examples.setdefault(key, detail)


def enumerate_windows(depth=0, code=0):
    global checked_edges
    counts[depth] += 1
    if depth == 10:
        raw_codes.append(code)
        raw_code_set.add(code)
        cls = raw[code]
        check(cls < 3741, 'raw_coverage', code)
        if cls >= 3741:
            return
        x, y = vertices[-1]
        last = word[-1]
        # The endpoint appears once in visits for the current arrival;
        # another appearance is an earlier departure vertex.
        revisited = visits[(x, y)] > 1
        affected_chunks = [entry for entry in chunk_stats.values()
                           if entry['first_affected_code'] <= code <= entry['last_affected_code']]
        for entry in affected_chunks:
            entry['raw_words'] += 1
            entry['classes'].add(cls)
            if len(entry['examples']) < 2:
                entry['examples'].append({'code': code, 'class': cls,
                                          'word': ''.join('ENWS'[d] for d in word)})
        for direction, (dx, dy) in enumerate(steps):
            target = (x + dx, y + dy)
            bond = tuple(sorted(((x, y), target)))
            allowed = direction != (last + 2) % 4 and bond not in bonds
            kind = 2 if revisited else (0 if direction == last else 1)
            check(representative_raw_kinds[cls][direction] == kind,
                  'all_direction_class_kind_compatibility', (code, cls, direction))
            stored_destination = destinations[4 * cls + direction]
            check((stored_destination != 0) == allowed, 'admissibility', (code, cls, direction))
            if allowed:
                checked_edges += 1
                for entry in affected_chunks:
                    entry['checked_admissible_edges'] += 1
                successor = (code % (4 ** 9)) * 4 + direction
                check(kinds[4 * cls + direction] == kind, 'kind', (code, cls, direction))
                check(stored_destination - 1 == raw[successor], 'successor', (code, cls, direction))
                if kind != 2:
                    check(representatives[cls] % 4 == last, 'arrival', (code, cls, direction))
        return
    x, y = vertices[-1]
    for direction, (dx, dy) in enumerate(steps):
        target = (x + dx, y + dy)
        bond = tuple(sorted(((x, y), target)))
        if bond in bonds:
            continue
        bonds.add(bond)
        vertices.append(target)
        word.append(direction)
        visits[target] += 1
        enumerate_windows(depth + 1, code * 4 + direction)
        visits[target] -= 1
        word.pop()
        vertices.pop()
        bonds.remove(bond)


enumerate_windows()
assert counts[1:] == [4, 12, 36, 108, 316, 916, 2628, 7500, 21268, 60092]
assert raw_codes == sorted(raw_codes) and len(raw_code_set) == 60092
check(all((value < 3741) == (code in raw_code_set) for code, value in enumerate(raw)),
      'invalid_word_coverage', None)
assert all(code in raw_code_set for code in representatives)
edge_counts = Counter(kind for destination, kind in zip(destinations, kinds) if destination)
check(edge_counts == Counter({0: 2516, 1: 5032, 2: 1872}), 'edge_counts', dict(edge_counts))

for entry in chunk_stats.values():
    entry['classes'] = len(entry['classes'])
    entry['invalid_words'] = entry['last_affected_code'] - entry['first_affected_code'] + 1 - entry['raw_words']
    lo, hi = entry['first_affected_code'], entry['last_affected_code']
    entry['coverage_mismatches'] = sum((raw[code] < 3741) != (code in raw_code_set)
                                       for code in range(lo, hi + 1))

# Reconstruct the archive layout specified by the paper: header, all raw
# code/class pairs in lexicographic order, then nine integers per class row.
archive_rows = ['60092 3741']
archive_rows += [f'{code} {raw[code]}' for code in raw_codes]
archive_rows += [' '.join(map(str, [representatives[cls]]
                              + [value - 1 for value in destinations[4 * cls:4 * cls + 4]]
                              + [value if value < 3 else -1 for value in kinds[4 * cls:4 * cls + 4]]))
                 for cls in range(3741)]
archive = ('\n'.join(archive_rows) + '\n').encode()
archive_sha = hashlib.sha256(archive).hexdigest()
declared_sha = re.search(r'Archive SHA-256: ([0-9a-f]{64})', TEXT)[1]

result = {
    'source': str(SOURCE),
    'literal_count': len(LITERALS),
    'all_literal_chunks_fit_without_overlap': True,
    'raw_counts_by_length': counts[1:],
    'covered_codes': len(raw),
    'valid_raw_words': len(raw_codes),
    'raw_admissible_edges_checked': checked_edges,
    'quotient_edge_counts': dict(edge_counts),
    'errors': dict(errors),
    'error_examples': examples,
    'assigned_chunks': chunk_stats,
    'reconstructed_archive_sha256': archive_sha,
    'declared_archive_sha256': declared_sha,
    'reconstructed_archive_matches_declared_sha256': archive_sha == declared_sha,
}
print(json.dumps(result, indent=2))
assert not errors
