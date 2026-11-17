"""Read-only reconstruction of Automaton10Data against the paper's contract."""
from collections import Counter
from pathlib import Path
import hashlib
import json
import re

SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
source = SOURCE.read_text()


def unpack_group(name, width, count):
    literals = {
        f'{name}_{m[1]}': m[2]
        for m in re.finditer(
            rf'^private noncomputable def {name}_(\d+) : ℕ := 0x([0-9a-fA-F]+)$',
            source, re.M)
    }
    expression = re.search(
        rf'^noncomputable def {name} : ℕ := (.+)$', source, re.M)[1]
    tokens = re.findall(r'\w+|<<<|[()+]', expression)
    cursor = 0

    def atom():
        nonlocal cursor
        token = tokens[cursor]
        cursor += 1
        if token == '(':
            result = addition()
            assert tokens[cursor] == ')'
            cursor += 1
            return result
        return ('literal', token)

    def shift():
        nonlocal cursor
        result = atom()
        while cursor < len(tokens) and tokens[cursor] == '<<<':
            cursor += 1
            amount = int(tokens[cursor])
            cursor += 1
            result = ('shift', result, amount)
        return result

    def addition():
        nonlocal cursor
        result = shift()
        while cursor < len(tokens) and tokens[cursor] == '+':
            cursor += 1
            result = ('add', result, shift())
        return result

    tree = addition()
    assert cursor == len(tokens)
    offsets = {}

    def evaluate(node, offset=0):
        if node[0] == 'literal':
            offsets[node[1]] = offset
            return int(literals[node[1]], 16)
        if node[0] == 'shift':
            return evaluate(node[1], offset + node[2]) << node[2]
        return evaluate(node[1], offset) + evaluate(node[2], offset)

    packed = evaluate(tree)
    # Independent concatenation comparison also checks every shift in the AST.
    assert packed == int(''.join(literals.values()), 16)
    assert packed < 1 << (width * count)
    data = packed.to_bytes((width * count + 7) // 8, 'little')
    lanes = []
    for index in range(count):
        bit = width * index
        start, remainder = divmod(bit, 8)
        size = (width + remainder + 7) // 8
        lanes.append((int.from_bytes(data[start:start + size], 'little') >> remainder)
                     & ((1 << width) - 1))
    return lanes, offsets, literals


raw, offsets, literals = unpack_group('rawClass', 12, 4 ** 10)
reps, _, _ = unpack_group('representatives', 20, 3741)
destinations, _, _ = unpack_group('destinations', 12, 3741 * 4)
kinds, _, _ = unpack_group('edgeKinds', 2, 3741 * 4)

# The paper's independent lexicographic extension recursion, with no initial
# incoming direction and no reuse of unoriented bonds.
steps = ((1, 0), (0, 1), (-1, 0), (0, -1))
counts = [0] * 11
words = {}


def generate(word=(), code=0, current=(0, 0), used=frozenset()):
    depth = len(word)
    counts[depth] += 1
    if depth == 10:
        words[code] = word
        return
    for direction, step in enumerate(steps):
        new = (current[0] + step[0], current[1] + step[1])
        bond = frozenset((current, new))
        if bond not in used:
            generate(word + (direction,), code * 4 + direction, new, used | {bond})


generate()
assert counts[1:] == [4, 12, 36, 108, 316, 916, 2628, 7500, 21268, 60092]
assert list(words) == sorted(words)
coverage_errors = [code for code, value in enumerate(raw)
                   if value > 3741 or ((value < 3741) != (code in words))]
assert not coverage_errors, coverage_errors[:10]


def model(word):
    current = (0, 0)
    used = set()
    departures = set()
    for direction in word:
        departures.add(current)
        step = steps[direction]
        new = (current[0] + step[0], current[1] + step[1])
        used.add(frozenset((current, new)))
        current = new
    is_revisit = current in departures
    allowed = []
    departure_kinds = []
    for direction, step in enumerate(steps):
        new = (current[0] + step[0], current[1] + step[1])
        allowed.append(direction != (word[-1] + 2) % 4
                       and frozenset((current, new)) not in used)
        departure_kinds.append(2 if is_revisit else (0 if direction == word[-1] else 1))
    return tuple(allowed), tuple(departure_kinds), word[-1]


assert len(set(reps)) == 3741
assert all(code in words and raw[code] == a for a, code in enumerate(reps))
representative_models = [model(words[code]) for code in reps]
edge_count = Counter()
for a, code in enumerate(reps):
    allowed, actual_kinds, arrival = representative_models[a]
    for direction in range(4):
        index = 4 * a + direction
        destination = destinations[index]
        kind = kinds[index]
        assert 0 <= destination <= 3741
        assert (destination == 0) == (kind == 3)
        assert (destination != 0) == allowed[direction]
        if allowed[direction]:
            successor_code = (code % (4 ** 9)) * 4 + direction
            assert successor_code in words
            assert destination - 1 == raw[successor_code]
            assert kind == actual_kinds[direction]
            edge_count[kind] += 1
assert edge_count == {0: 2516, 1: 5032, 2: 1872}

# Check every raw word against its representative, including kinds on all four
# directions, and the final-direction obligation only on non-revisit edges.
for code, word in words.items():
    a = raw[code]
    allowed, actual_kinds, arrival = model(word)
    rep_allowed, rep_kinds, rep_arrival = representative_models[a]
    assert allowed == rep_allowed, (code, a, 'admissibility')
    assert actual_kinds == rep_kinds, (code, a, 'kind')
    for direction in range(4):
        if allowed[direction]:
            successor_code = (code % (4 ** 9)) * 4 + direction
            assert successor_code in words
            assert destinations[4 * a + direction] - 1 == raw[successor_code], (code, a, direction)
            if actual_kinds[direction] != 2:
                assert arrival == rep_arrival, (code, a, 'arrival')

result = {
    'source_sha256': hashlib.sha256(source.encode()).hexdigest(),
    'window_counts': counts[1:],
    'coverage_lanes_checked': len(raw),
    'raw_classes': len({raw[code] for code in words}),
    'representatives_checked': len(reps),
    'raw_direction_checks': len(words) * 4,
    'edge_counts': dict(sorted(edge_count.items())),
    'targets': [],
}
for number in range(50, 55):
    name = f'rawClass_{number}'
    low_bit = offsets[name]
    high_bit = low_bit + 4 * len(literals[name]) - 1
    low_code, high_code = low_bit // 12, high_bit // 12
    valid = [code for code in range(low_code, high_code + 1) if code in words]
    result['targets'].append({
        'declaration': name,
        'hex_digits': len(literals[name]),
        'bit_interval_inclusive': [low_bit, high_bit],
        'code_interval_inclusive': [low_code, high_code],
        'lanes_touched': high_code - low_code + 1,
        'valid_words': len(valid),
        'invalid_words': high_code - low_code + 1 - len(valid),
        'distinct_classes': len({raw[code] for code in valid}),
        'boundary_lane_bits': [low_bit % 12, (high_bit + 1) % 12],
        'first_valid_example': None if not valid else {
            'code': valid[0], 'word': ''.join('ENWS'[d] for d in words[valid[0]]),
            'class': raw[valid[0]], 'representative_code': reps[raw[valid[0]]]},
    })
print(json.dumps(result, indent=2))
