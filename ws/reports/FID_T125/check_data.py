"""Read-only reconstruction of the paper's memory-ten finite checks."""

from collections import Counter
from pathlib import Path
import hashlib
import json
import re


SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
source = SOURCE.read_text()
lines = source.splitlines()
literals = {}
locations = {}
expressions = {}
for line_number, line in enumerate(lines, 1):
    match = re.fullmatch(r'private noncomputable def (\w+) : ℕ := 0x([0-9a-f]+)', line)
    if match:
        literals[match[1]] = int(match[2], 16)
        locations[match[1]] = line_number
    match = re.fullmatch(r'noncomputable def (rawClass|representatives|destinations|edgeKinds) : ℕ := (.*)', line)
    if match:
        expressions[match[1]] = match[2]


def parse(expression):
    tokens = re.findall(r'<<<|[()+]|\w+', expression)
    cursor = 0

    def atom():
        nonlocal cursor
        token = tokens[cursor]
        cursor += 1
        if token == '(':
            result = term()
            assert tokens[cursor] == ')'
            cursor += 1
            return result
        return ('value', token)

    def term():
        nonlocal cursor
        result = atom()
        while cursor < len(tokens) and tokens[cursor] != ')':
            operation = tokens[cursor]
            cursor += 1
            result = (operation, result, atom())
        return result

    result = term()
    assert cursor == len(tokens)
    assert ''.join(tokens) == re.sub(r'\s+', '', expression)
    return result


def flatten(tree, offset=0):
    if tree[0] == 'value':
        return [(tree[1], offset)]
    if tree[0] == '+':
        return flatten(tree[1], offset) + flatten(tree[2], offset)
    assert tree[0] == '<<<' and tree[2][0] == 'value'
    return flatten(tree[1], offset + int(tree[2][1]))


tables = {}
offsets = {}
for name, expression in expressions.items():
    leaves = flatten(parse(expression))
    assert len(leaves) == len(set(leaf for leaf, _ in leaves))
    assert {leaf for leaf, _ in leaves} == {key for key in literals if key.startswith(name + '_')}
    previous_end = 0
    for leaf, offset in sorted(leaves, key=lambda pair: pair[1]):
        assert offset >= previous_end, (leaf, 'overlapping nonzero bits')
        previous_end = offset + literals[leaf].bit_length()
    packed = sum(literals[leaf] << offset for leaf, offset in leaves)
    tables[name] = packed.to_bytes((packed.bit_length() + 7) // 8, 'little')
    offsets.update(leaves)


def lane(table, width, index):
    bit = width * index
    start = bit // 8
    length = (bit % 8 + width + 7) // 8
    return (int.from_bytes(tables[table][start:start + length], 'little') >> (bit % 8)) & ((1 << width) - 1)


steps = ((1, 0), (0, 1), (-1, 0), (0, -1))
counts = [0] * 11
raw_words = {}


def extend(word, vertices, used_bonds, code):
    depth = len(word)
    counts[depth] += 1
    if depth == 10:
        raw_words[code] = (word, vertices, used_bonds)
        return
    x, y = vertices[-1]
    for direction, (dx, dy) in enumerate(steps):
        new_vertex = (x + dx, y + dy)
        bond = frozenset((vertices[-1], new_vertex))
        if bond not in used_bonds:
            extend(word + (direction,), vertices + (new_vertex,), used_bonds | {bond}, code * 4 + direction)


extend((), ((0, 0),), frozenset(), 0)
assert counts == [1, 4, 12, 36, 108, 316, 916, 2628, 7500, 21268, 60092]

mapping = [lane('rawClass', 12, code) for code in range(4**10)]
coverage_errors = [code for code, value in enumerate(mapping) if
                   value > 3741 or (value < 3741) != (code in raw_words)]
assert not coverage_errors, coverage_errors[:10]
representatives = [lane('representatives', 20, state) for state in range(3741)]
assert len(set(representatives)) == 3741
assert all(code < 4**10 and code in raw_words and mapping[code] == state
           for state, code in enumerate(representatives))
assert set(mapping[code] for code in raw_words) == set(range(3741))


def signature(code):
    word, vertices, used_bonds = raw_words[code]
    x, y = vertices[-1]
    revisit = vertices[-1] in vertices[:-1]
    kinds = tuple(2 if revisit else 0 if d == word[-1] else 1 for d in range(4))
    admissible = tuple(d != (word[-1] + 2) % 4 and
                       frozenset((vertices[-1], (x + dx, y + dy))) not in used_bonds
                       for d, (dx, dy) in enumerate(steps))
    successors = tuple((code % (4**9)) * 4 + d for d in range(4))
    return admissible, kinds, successors, word[-1]


signatures = {code: signature(code) for code in raw_words}
representative_signatures = [signatures[code] for code in representatives]
edge_counts = Counter()
for state in range(3741):
    admissible, kinds, successors, arrival = representative_signatures[state]
    assert representatives[state] % 4 == arrival
    for direction in range(4):
        index = state * 4 + direction
        destination = lane('destinations', 12, index)
        kind = lane('edgeKinds', 2, index)
        assert destination <= 3741
        assert (destination == 0) == (kind == 3)
        assert (destination != 0) == admissible[direction]
        if admissible[direction]:
            assert successors[direction] in raw_words
            assert destination == mapping[successors[direction]] + 1
            assert kind == kinds[direction]
            edge_counts[kind] += 1
assert edge_counts == {0: 2516, 1: 5032, 2: 1872}

checked_directions = 0
for code in raw_words:
    state = mapping[code]
    admissible, kinds, successors, arrival = signatures[code]
    rep_allowed, rep_kinds, rep_successors, rep_arrival = representative_signatures[state]
    # Also check kind agreement on inadmissible directions, as in the paper's lemma.
    assert admissible == rep_allowed
    assert kinds == rep_kinds
    for direction in range(4):
        checked_directions += 1
        if admissible[direction]:
            assert successors[direction] in raw_words
            assert mapping[successors[direction]] == mapping[rep_successors[direction]]
            if kinds[direction] != 2:
                assert arrival == rep_arrival

targets = []
for part in range(590, 595):
    name = f'rawClass_{part}'
    low = offsets[name]
    high = low + 16384
    first = low // 12
    last = (high - 1) // 12
    codes = range(first, last + 1)
    raw_codes = [code for code in codes if code in raw_words]
    invalid_codes = [code for code in codes if code not in raw_words]
    assert all(mapping[code] == 3741 for code in invalid_codes)
    samples = raw_codes[:3]
    # Recover the whole literal from its actual packed bit interval, including boundary lanes.
    start = low // 8
    size = (low % 8 + 16384 + 7) // 8
    extracted = (int.from_bytes(tables['rawClass'][start:start+size], 'little') >> (low % 8)) & ((1 << 16384) - 1)
    assert extracted == literals[name]
    targets.append({
        'declaration': name,
        'line': locations[name],
        'bit_interval_half_open': [low, high],
        'touched_code_interval_inclusive': [first, last],
        'complete_lanes': (high // 12) - ((low + 11) // 12),
        'valid_touched_codes': len(raw_codes),
        'invalid_touched_codes': len(invalid_codes),
        'distinct_classes_touched': len({mapping[code] for code in raw_codes}),
        'samples': [{'code': code, 'word': ''.join('ENWS'[d] for d in raw_words[code][0]),
                     'class': mapping[code], 'representative': representatives[mapping[code]]}
                    for code in samples],
        'literal_sha256_big_endian_2048_bytes': hashlib.sha256(literals[name].to_bytes(2048, 'big')).hexdigest(),
    })

result = {
    'raw_counts_depth_0_through_10': counts,
    'all_word_codes_checked': 4**10,
    'representatives_checked': len(representatives),
    'raw_direction_checks': checked_directions,
    'quotient_edge_counts_straight_turn_revisit': [edge_counts[k] for k in range(3)],
    'targets': targets,
    'result': 'All reconstruction assertions passed',
}
print(json.dumps(result, indent=2))
