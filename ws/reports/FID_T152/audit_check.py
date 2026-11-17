"""Read-only reconstruction of the supplied automaton's finite contracts."""

import ast
from collections import Counter
from pathlib import Path
import re

ROOT = Path('/home/ubuntu/aklt/review/FID_T/lean')
SOURCE = ROOT / 'AKLT/Defs/Automaton10Data.lean'
text = SOURCE.read_text()
literals = {}
digits = {}
expressions = {}
line_numbers = {}
for line_number, line in enumerate(text.splitlines(), 1):
    match = re.fullmatch(r'(?:private )?noncomputable def (\w+) : ℕ := (.+)', line)
    if match:
        name, expression = match.groups()
        line_numbers[name] = line_number
        if re.fullmatch(r'0x[0-9a-f]+', expression):
            literals[name] = int(expression, 16)
            digits[name] = len(expression) - 2
        else:
            expressions[name] = expression


def evaluate(node):
    """Return the exact natural value and each literal's low-bit offset."""
    if isinstance(node, ast.Name):
        return literals[node.id], {node.id: 0}
    if isinstance(node, ast.Constant):
        assert isinstance(node.value, int) and node.value >= 0
        return node.value, {}
    assert isinstance(node, ast.BinOp), ast.dump(node)
    left, left_offsets = evaluate(node.left)
    right, right_offsets = evaluate(node.right)
    if isinstance(node.op, ast.LShift):
        assert not right_offsets
        return left << right, {key: offset + right for key, offset in left_offsets.items()}
    assert isinstance(node.op, ast.Add), ast.dump(node)
    assert not left_offsets.keys() & right_offsets.keys()
    return left + right, left_offsets | right_offsets


tables = {}
offsets = {}
for name, expression in expressions.items():
    tables[name], offsets[name] = evaluate(ast.parse(expression.replace('<<<', '<<'), mode='eval').body)
    intervals = sorted((offset, offset + 4 * digits[key], key) for key, offset in offsets[name].items())
    assert intervals[0][0] == 0
    for first, second in zip(intervals, intervals[1:]):
        assert first[1] == second[0], (first, second)
    assert all(literals[key] < 1 << (end - begin) for begin, end, key in intervals)
    print('PACKING', name, 'chunks', len(intervals), 'width', intervals[-1][1],
          'actual_bit_length', tables[name].bit_length(), 'contiguous, no overlap/carry')


def lanes(name, width, count):
    value = tables[name]
    assert value < 1 << (width * count)
    raw = value.to_bytes((width * count + 7) // 8, 'little')
    mask = (1 << width) - 1
    result = []
    for index in range(count):
        byte, bit = divmod(width * index, 8)
        size = (bit + width + 7) // 8
        result.append((int.from_bytes(raw[byte:byte + size], 'little') >> bit) & mask)
    return result


classes = lanes('rawClass', 12, 4**10)
reps = lanes('representatives', 20, 3741)
destinations = lanes('destinations', 12, 3741 * 4)
kinds = lanes('edgeKinds', 2, 3741 * 4)
print('RAW_LANE_COUNTS', sorted(Counter(classes).items())[-3:], 'min', min(classes),
      'max', max(classes), 'non_sentinel', sum(a != 3741 for a in classes))

STEPS = ((1, 0), (0, 1), (-1, 0), (0, -1))


def bond(x, y):
    return (x, y) if x < y else (y, x)


def decode(code):
    return tuple((code // 4**(9-i)) % 4 for i in range(10))


def geometry(word):
    point = (0, 0)
    used = set()
    departures = set()
    for direction in word:
        departures.add(point)
        delta = STEPS[direction]
        new_point = (point[0] + delta[0], point[1] + delta[1])
        edge = bond(point, new_point)
        if edge in used:
            return None
        used.add(edge)
        point = new_point
    return point, used, departures


generated = {}
counts = [0] * 11


def generate(word, code, point, used, departures):
    depth = len(word)
    counts[depth] += 1
    if depth == 10:
        generated[code] = (word, point, used, departures)
        return
    for direction, delta in enumerate(STEPS):
        new_point = (point[0] + delta[0], point[1] + delta[1])
        edge = bond(point, new_point)
        if edge not in used:
            generate(word + (direction,), code * 4 + direction, new_point,
                     used | {edge}, departures | {point})


generate((), 0, (0, 0), set(), set())
print('GENERATED_DEPTH_COUNTS', counts)
errors = []
coverage_errors = []
for code, a in enumerate(classes):
    if a > 3741 or ((a < 3741) != (code in generated)):
        coverage_errors.append((code, a, code in generated))
print('COVERAGE_ERRORS', len(coverage_errors), coverage_errors[:12])
errors.extend(('coverage', error) for error in coverage_errors)

representative_errors = []
for a, code in enumerate(reps):
    if code >= 4**10 or code not in generated or classes[code] != a:
        representative_errors.append((a, code, classes[code] if code < 4**10 else None))
print('REPRESENTATIVE_ERRORS', len(representative_errors), representative_errors[:12])
errors.extend(('representative', error) for error in representative_errors)

format_errors = []
for index, (destination, kind) in enumerate(zip(destinations, kinds)):
    if destination > 3741 or (destination == 0) != (kind == 3):
        format_errors.append((index // 4, index % 4, destination, kind))
print('EDGE_FORMAT_ERRORS', len(format_errors), format_errors[:12])
errors.extend(('edge_format', error) for error in format_errors)

row_errors = []
unrestricted_kind_errors = []
for code, (word, point, used, departures) in generated.items():
    a = classes[code] % 3741
    representative = decode(reps[a])
    representative_geometry = geometry(representative)
    rep_revisit = representative_geometry is not None and representative_geometry[0] in representative_geometry[2]
    revisit = point in departures
    for direction, delta in enumerate(STEPS):
        new_point = (point[0] + delta[0], point[1] + delta[1])
        admissible = direction != (word[-1] + 2) % 4 and bond(point, new_point) not in used
        kind = 2 if revisit else (0 if direction == word[-1] else 1)
        representative_kind = 2 if rep_revisit else (0 if direction == representative[-1] else 1)
        if kind != representative_kind:
            unrestricted_kind_errors.append((code, a, direction, kind, representative_kind))
        index = a * 4 + direction
        if (destinations[index] != 0) != admissible:
            row_errors.append((code, a, direction, 'admissibility', admissible, destinations[index]))
        if admissible:
            successor_code = (code % 4**9) * 4 + direction
            successor = classes[successor_code] % 3741
            stored_successor = max(destinations[index] - 1, 0) % 3741
            if kinds[index] != kind:
                row_errors.append((code, a, direction, 'kind', kind, kinds[index]))
            if stored_successor != successor:
                row_errors.append((code, a, direction, 'successor', successor, stored_successor))
            if kind != 2 and reps[a] % 4 != word[-1]:
                row_errors.append((code, a, direction, 'arrival', word[-1], reps[a] % 4))
print('RAW_TO_QUOTIENT_ROW_ERRORS', len(row_errors), row_errors[:20])
print('UNRESTRICTED_REPRESENTATIVE_KIND_ERRORS', len(unrestricted_kind_errors), unrestricted_kind_errors[:12])
errors.extend(('row', error) for error in row_errors)
errors.extend(('unrestricted_kind', error) for error in unrestricted_kind_errors)
edge_counts = Counter(kinds[index] for index, destination in enumerate(destinations) if destination != 0)
print('ADMISSIBLE_EDGE_COUNTS', dict(sorted(edge_counts.items())))

for number in range(725, 730):
    name = 'rawClass_' + str(number)
    low = offsets['rawClass'][name]
    high = low + 4 * digits[name]
    code_low = low // 12
    code_high = (high - 1) // 12
    covered = range(code_low, code_high + 1)
    valid = [code for code in covered if code in generated]
    local_errors = [error for error in coverage_errors if error[0] in covered]
    local_rows = [error for error in row_errors if error[0] in covered]
    print('TARGET', name, 'source_line', line_numbers[name], 'bits', (low, high - 1),
          'codes_inclusive', (code_low, code_high), 'valid', len(valid),
          'invalid', code_high - code_low + 1 - len(valid),
          'coverage_errors', len(local_errors), 'row_errors', len(local_rows))
    print('  ENDPOINT_LANES', [(code, classes[code], code in generated) for code in (code_low, code_high)])
    sample = valid[:3] + valid[-3:] if len(valid) > 6 else valid
    print('  VALID_SAMPLES', [(code, ''.join('ENWS'[d] for d in decode(code)), classes[code]) for code in sample])

print('TOTAL_ERRORS', len(errors))
assert counts == [1, 4, 12, 36, 108, 316, 916, 2628, 7500, 21268, 60092]
assert edge_counts == {0: 2516, 1: 5032, 2: 1872}
assert not errors
