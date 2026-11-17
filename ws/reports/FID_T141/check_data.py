"""Read-only reconstruction of the supplied Lean literal tables.

The only input is Automaton10Data.lean.  Trail enumeration is independent
of its stored map and follows app-input-contracts.tex's used-bond recursion.
"""

from collections import Counter
from pathlib import Path
import re

SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
text = SOURCE.read_text()
literals = {}
locations = {}
expressions = {}
for line_no, line in enumerate(text.splitlines(), 1):
    match = re.fullmatch(r'private noncomputable def (\w+) : ℕ := 0x([0-9a-f]+)', line)
    if match:
        name, digits = match.groups()
        literals[name] = (int(digits, 16), len(digits) * 4)
        locations[name] = line_no
    match = re.fullmatch(r'noncomputable def (\w+) : ℕ := (.*)', line)
    if match:
        expressions[match[1]] = match[2]


def parse(expression):
    tokens = re.findall(r'<<<|\w+|[()+]', expression)
    assert ''.join(tokens) == re.sub(r'\s', '', expression)
    position = 0

    def atom():
        nonlocal position
        token = tokens[position]
        position += 1
        if token != '(':
            return int(token) if token.isdecimal() else token
        left = atom()
        if tokens[position] == ')':
            position += 1
            return left
        op = tokens[position]
        position += 1
        assert op in ('+', '<<<')
        right = atom()
        assert tokens[position] == ')'
        position += 1
        return (op, left, right)

    tree = atom()
    assert position == len(tokens)
    return tree


def evaluate(tree):
    if isinstance(tree, int):
        return tree
    if isinstance(tree, str):
        return literals[tree][0]
    op, left, right = tree
    a, b = evaluate(left), evaluate(right)
    return a + b if op == '+' else a << b


def leaves(tree, offset=0):
    if isinstance(tree, str):
        return [(tree, offset)]
    op, left, right = tree
    if op == '<<<':
        assert isinstance(right, int)
        return leaves(left, offset + right)
    return leaves(left, offset) + leaves(right, offset)


tables = {}
offsets = {}
for name, expression in expressions.items():
    tree = parse(expression)
    value = evaluate(tree)
    tables[name] = value.to_bytes((value.bit_length() + 7) // 8, 'little')
    positions = leaves(tree)
    assert len({n for n, _ in positions}) == len(positions)
    for literal, offset in positions:
        assert literal not in offsets
        offsets[literal] = offset
    ordered = sorted(positions, key=lambda item: item[1])
    assert ordered[0][1] == 0
    for (lower, lo), (_, hi) in zip(ordered, ordered[1:]):
        assert lo + literals[lower][1] == hi, (lower, lo, hi)
    print(f'TABLE {name}: {len(positions)} contiguous nonoverlapping chunks; '
          f'{value.bit_length()} significant bits')
assert set(literals) == set(offsets)


def lane(table, width, index):
    bit = width * index
    data = tables[table][bit // 8:(bit + width + 7) // 8]
    return (int.from_bytes(data, 'little') >> (bit % 8)) & ((1 << width) - 1)


raw = [lane('rawClass', 12, code) for code in range(4 ** 10)]
assert all(value <= 3741 for value in raw)
steps = ((1, 0), (0, 1), (-1, 0), (0, -1))
counts = [0] * 11
windows = {}


def enumerate_windows(code, word, position, bonds, departures):
    length = len(word)
    counts[length] += 1
    if length == 10:
        assert code not in windows
        windows[code] = (word, position, bonds, departures)
        return
    for direction, (dx, dy) in enumerate(steps):
        endpoint = (position[0] + dx, position[1] + dy)
        bond = tuple(sorted((position, endpoint)))
        if bond not in bonds:
            enumerate_windows(code * 4 + direction, word + (direction,), endpoint,
                              bonds | {bond}, departures | {position})


enumerate_windows(0, (), (0, 0), frozenset(), frozenset())
assert counts == [1, 4, 12, 36, 108, 316, 916, 2628, 7500, 21268, 60092]
valid_codes = set(windows)
coverage_errors = [code for code, value in enumerate(raw)
                   if (value < 3741) != (code in valid_codes)]
assert not coverage_errors, coverage_errors[:10]
print(f'RAW COVERAGE: {counts[10]} valid codes, {4 ** 10 - counts[10]} sentinel codes; no mismatches')
print(f'INDEPENDENT PREFIX COUNTS: {counts[1:]}')


def row(code):
    word, position, bonds, departures = windows[code]
    result = []
    for direction, (dx, dy) in enumerate(steps):
        endpoint = (position[0] + dx, position[1] + dy)
        bond = tuple(sorted((position, endpoint)))
        if direction == (word[-1] + 2) % 4 or bond in bonds:
            result.append(None)
            continue
        kind = 2 if position in departures else (0 if direction == word[-1] else 1)
        successor = (code % (4 ** 9)) * 4 + direction
        assert successor in valid_codes
        result.append((kind, raw[successor]))
    return result


representatives = [lane('representatives', 20, cls) for cls in range(3741)]
edge_counts = Counter()
for cls, code in enumerate(representatives):
    assert code < 4 ** 10 and code in valid_codes and raw[code] == cls
    for direction, edge in enumerate(row(code)):
        destination = lane('destinations', 12, cls * 4 + direction)
        kind = lane('edgeKinds', 2, cls * 4 + direction)
        assert destination <= 3741
        if edge is None:
            assert (destination, kind) == (0, 3)
        else:
            assert (kind, destination - 1) == edge
            edge_counts[kind] += 1
assert [edge_counts[kind] for kind in range(3)] == [2516, 5032, 1872]
for code, (word, _, _, _) in windows.items():
    cls = raw[code]
    for direction, edge in enumerate(row(code)):
        destination = lane('destinations', 12, cls * 4 + direction)
        kind = lane('edgeKinds', 2, cls * 4 + direction)
        if edge is None:
            assert destination == 0
        else:
            assert destination != 0 and (kind, destination - 1) == edge
            if kind != 2:
                assert word[-1] == representatives[cls] % 4
print(f'QUOTIENT: 3741 representatives and all 60092 raw rows agree; edge counts {dict(sorted(edge_counts.items()))}')


def digits(code):
    return ''.join(str((code >> (2 * (9 - i))) & 3) for i in range(10))


for index in range(670, 675):
    name = f'rawClass_{index}'
    value, width = literals[name]
    offset = offsets[name]
    first = offset // 12
    last = (offset + width - 1) // 12
    codes = range(first, last + 1)
    assert not any(code in valid_codes for code in codes)
    assert all(raw[code] == 3741 for code in codes)
    # Compare every literal bit, including both partial boundary lanes,
    # against the infinite 12-bit repetition of sentinel 3741 = 0xe9d.
    lane_count = (width + offset % 12 + 11) // 12
    sentinel_run = 3741 * ((1 << (12 * lane_count)) - 1) // ((1 << 12) - 1)
    expected = (sentinel_run >> (offset % 12)) & ((1 << width) - 1)
    assert value == expected
    # Produce a short independent invalidity witness for every affected code.
    reversals = Counter()
    for code in codes:
        word = tuple(map(int, digits(code)))
        reversal = next((i for i in range(9) if word[i + 1] == (word[i] + 2) % 4), None)
        assert reversal is not None
        reversals[reversal + 1] += 1  # first step of reversed pair, 1-based
    print(f'DECL {name} line={locations[name]} width={width} '
          f'bits={offset}..{offset + width - 1} phase={offset % 12} '
          f'codes={first}..{last} ({len(codes)} codes) '
          f'base4={digits(first)}..{digits(last)} '
          f'all_sentinel_exact=True first_reversal_step_counts={dict(sorted(reversals.items()))}')
