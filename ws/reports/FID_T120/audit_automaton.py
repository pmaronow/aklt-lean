"""Read-only reconstruction of the supplied Lean automaton literals.

Run with python3 from this directory. No Lean process or archive is needed.
"""

from collections import Counter
import hashlib
import json
from pathlib import Path
import re


SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
text = SOURCE.read_text()
literals = {}
source_lines = {}
expressions = {}
for line_number, line in enumerate(text.splitlines(), 1):
    match = re.fullmatch(r'private noncomputable def (\w+) : ℕ := 0x([0-9a-f]+)', line)
    if match:
        name, digits = match.groups()
        literals[name] = int(digits, 16)
        source_lines[name] = line_number
    match = re.fullmatch(r'noncomputable def (\w+) : ℕ := (.+)', line)
    if match:
        expressions[match[1]] = match[2]


def parse(expression):
    tokens = re.findall(r'\w+|<<<|[()+]', expression)
    assert ''.join(tokens) == re.sub(r'\s', '', expression)
    position = 0

    def atom():
        nonlocal position
        token = tokens[position]
        position += 1
        if token == '(':
            result = expr()
            assert tokens[position] == ')'
            position += 1
            return result
        if token.isdecimal():
            return int(token)
        assert token in literals
        return token

    def expr():
        nonlocal position
        result = atom()
        # Every unparenthesized expression uses just one of the operators.
        operations = set()
        while position < len(tokens) and tokens[position] in ('+', '<<<'):
            operation = tokens[position]
            operations.add(operation)
            assert len(operations) == 1, 'Would need Lean precedence resolution'
            position += 1
            result = (operation, result, atom())
        return result

    result = expr()
    assert position == len(tokens)
    return result


def evaluate(node):
    if isinstance(node, int):
        return node
    if isinstance(node, str):
        return literals[node]
    operation, left, right = node
    if operation == '+':
        return evaluate(left) + evaluate(right)
    return evaluate(left) << evaluate(right)


def leaf_offsets(node, offset=0):
    if isinstance(node, str):
        return [(node, offset)]
    operation, left, right = node
    if operation == '+':
        return leaf_offsets(left, offset) + leaf_offsets(right, offset)
    return leaf_offsets(left, offset + evaluate(right))


trees = {name: parse(expression) for name, expression in expressions.items()}
packed = {name: evaluate(tree) for name, tree in trees.items()}
offsets = dict(leaf_offsets(trees['rawClass']))
assert len(offsets) == 768
assert len(literals) == 768 + 5 + 11 + 2
ordered = sorted(offsets.items(), key=lambda item: item[1])
assert ordered[0] == ('rawClass_767', 0)
for (name, offset), (_, next_offset) in zip(ordered, ordered[1:]):
    assert literals[name] < 1 << (next_offset - offset)
assert packed['rawClass'].bit_length() <= 12 * 4**10


def lanes(name, width, count):
    blob = packed[name].to_bytes((width * count + 7) // 8, 'little')
    mask = (1 << width) - 1
    return [
        (int.from_bytes(blob[(width * i) // 8:(width * i + width + 7) // 8], 'little')
         >> ((width * i) % 8)) & mask
        for i in range(count)
    ]


classes = lanes('rawClass', 12, 4**10)
representatives = lanes('representatives', 20, 3741)
destinations = lanes('destinations', 12, 4 * 3741)
kinds = lanes('edgeKinds', 2, 4 * 3741)
assert all(0 <= value <= 3741 for value in classes)
assert all(value < 4**10 for value in representatives)
assert all(value <= 3741 for value in destinations)
assert all((destination == 0) == (kind == 3)
           for destination, kind in zip(destinations, kinds))

steps = ((1, 0), (0, 1), (-1, 0), (0, -1))
raw = {}
depth_counts = Counter()


def edge(u, v):
    return tuple(sorted((u, v)))


def generate(word, vertices, used, code):
    depth_counts[len(word)] += 1
    endpoint = vertices[-1]
    if len(word) == 10:
        revisit = endpoint in vertices[:-1]
        allowed = []
        row_kinds = []
        for direction, (dx, dy) in enumerate(steps):
            new_vertex = (endpoint[0] + dx, endpoint[1] + dy)
            allowed.append(direction != (word[-1] + 2) % 4
                           and edge(endpoint, new_vertex) not in used)
            row_kinds.append(2 if revisit else 0 if direction == word[-1] else 1)
        raw[code] = (tuple(allowed), tuple(row_kinds), word[-1])
        return
    for direction, (dx, dy) in enumerate(steps):
        new_vertex = (endpoint[0] + dx, endpoint[1] + dy)
        bond = edge(endpoint, new_vertex)
        if bond not in used:
            generate(word + (direction,), vertices + (new_vertex,), used | {bond},
                     4 * code + direction)


generate((), ((0, 0),), set(), 0)
assert [depth_counts[d] for d in range(1, 11)] == [
    4, 12, 36, 108, 316, 916, 2628, 7500, 21268, 60092]
assert all((value < 3741) == (code in raw) for code, value in enumerate(classes))
assert all(rep in raw and classes[rep] == a for a, rep in enumerate(representatives))
assert len(set(classes[code] for code in raw)) == 3741

admitted_raw_checks = 0
all_direction_kind_checks = 0
for code, (allowed, row_kinds, arrival) in raw.items():
    a = classes[code]
    rep_allowed, rep_kinds, rep_arrival = raw[representatives[a]]
    # Includes the paper's kind comparison for all four absolute directions.
    assert row_kinds == rep_kinds
    all_direction_kind_checks += 4
    assert allowed == rep_allowed
    for direction in range(4):
        index = 4 * a + direction
        assert allowed[direction] == (destinations[index] != 0)
        if allowed[direction]:
            admitted_raw_checks += 1
            assert kinds[index] == row_kinds[direction]
            successor = 4 * (code % 4**9) + direction
            assert successor in raw
            assert destinations[index] - 1 == classes[successor]
            if row_kinds[direction] != 2:
                assert arrival == rep_arrival == representatives[a] % 4

edge_counts = Counter(kind for destination, kind in zip(destinations, kinds) if destination)
assert edge_counts == Counter({0: 2516, 1: 5032, 2: 1872})

# Recover the text file described by the paper, including its signed sentinels.
archive_lines = ['60092 3741\n']
archive_lines.extend(f'{code} {classes[code]}\n' for code in sorted(raw))
for a, representative in enumerate(representatives):
    row_destinations = [destinations[4 * a + d] - 1 for d in range(4)]
    row_kinds = [-1 if kinds[4 * a + d] == 3 else kinds[4 * a + d] for d in range(4)]
    archive_lines.append(' '.join(map(str, [representative] + row_destinations + row_kinds)) + '\n')
archive_sha256 = hashlib.sha256(''.join(archive_lines).encode()).hexdigest()
recorded_archive_sha256 = re.search(r'Archive SHA-256: ([0-9a-f]{64})', text)[1]
assert archive_sha256 == recorded_archive_sha256

chunks = []
for number in range(565, 570):
    name = f'rawClass_{number}'
    lo = offsets[name]
    hi = lo + 16384
    first = lo // 12
    last = (hi - 1) // 12
    fully_first = (lo + 11) // 12
    fully_last = hi // 12 - 1
    valid = [code for code in range(first, last + 1) if code in raw]
    chunks.append({
        'declaration': name,
        'line': source_lines[name],
        'bit_interval': [lo, hi],
        'overlapping_code_interval': [first, last],
        'fully_contained_code_interval': [fully_first, fully_last],
        'valid_overlapping_words': len(valid),
        'invalid_overlapping_words': last - first + 1 - len(valid),
        'class_range_on_valid_words': ([min(classes[c] for c in valid),
                                       max(classes[c] for c in valid)] if valid else None),
        'first_valid_examples': [[code, classes[code]] for code in valid[:3]],
        'last_valid_examples': [[code, classes[code]] for code in valid[-3:]],
    })

print(json.dumps({
    'source_sha256': hashlib.sha256(text.encode()).hexdigest(),
    'reconstructed_archive_sha256': archive_sha256,
    'literal_counts': len(literals),
    'raw_window_count': len(raw),
    'class_count': len(set(classes[code] for code in raw)),
    'invalid_word_count': len(classes) - len(raw),
    'admissible_raw_transition_checks': admitted_raw_checks,
    'all_direction_kind_checks': all_direction_kind_checks,
    'quotient_edge_counts': dict(edge_counts),
    'chunks': chunks,
    'result': 'all assertions passed',
}, indent=2))
