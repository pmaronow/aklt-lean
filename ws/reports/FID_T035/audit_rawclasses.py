"""Read-only reconstruction of the permitted Lean literals and paper contracts."""

from collections import Counter
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
source = SOURCE.read_text()
constants = {}
expressions = {}
source_lines = {}
for line_number, line in enumerate(source.splitlines(), 1):
    match = re.fullmatch(r'(?:private )?noncomputable def (\w+) : ℕ := (.+)', line)
    if match:
        name, expression = match.groups()
        source_lines[name] = line_number
        if re.fullmatch(r'0x[0-9a-f]+', expression):
            constants[name] = int(expression, 16)
        else:
            expressions[name] = expression


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
        return int(token) if token.isdecimal() else token

    def expr():
        nonlocal position
        left = atom()
        # The exporter explicitly parenthesizes every binary expression.
        if position < len(tokens) and tokens[position] in ('+', '<<<'):
            operation = tokens[position]
            position += 1
            left = (operation, left, atom())
        return left

    result = expr()
    assert position == len(tokens)
    return result


def evaluate(node):
    if isinstance(node, int):
        return node
    if isinstance(node, str):
        return constants[node]
    operation, left, right = node
    if operation == '+':
        return evaluate(left) + evaluate(right)
    assert operation == '<<<'
    return evaluate(left) << evaluate(right)


def offsets(node, offset=0):
    if isinstance(node, str):
        return {node: offset}
    assert isinstance(node, tuple)
    operation, left, right = node
    if operation == '<<<':
        return offsets(left, offset + evaluate(right))
    assert operation == '+'
    lhs, rhs = offsets(left, offset), offsets(right, offset)
    assert not lhs.keys() & rhs.keys()
    return lhs | rhs


trees = {name: parse(expression) for name, expression in expressions.items()}
packed = {name: evaluate(tree) for name, tree in trees.items()}
leaf_offsets = {name: offsets(tree) for name, tree in trees.items()}
packed_bytes = {
    name: value.to_bytes((value.bit_length() + 7) // 8, 'little')
    for name, value in packed.items()
}
for name, mapping in leaf_offsets.items():
    ordered = sorted(mapping.items(), key=lambda pair: pair[1])
    assert ordered[0][1] == 0
    for (lower, offset), (_, next_offset) in zip(ordered, ordered[1:]):
        assert constants[lower].bit_length() <= next_offset - offset, lower


def lane(name, width, index):
    bit_offset = width * index
    byte_offset, remainder = divmod(bit_offset, 8)
    part = packed_bytes[name][byte_offset:byte_offset + (remainder + width + 7) // 8]
    return (int.from_bytes(part, 'little') >> remainder) & ((1 << width) - 1)


raw = [lane('rawClass', 12, code) for code in range(4**10)]
representatives = [lane('representatives', 20, a) for a in range(3741)]
destinations = [[lane('destinations', 12, 4*a+d) for d in range(4)] for a in range(3741)]
kinds = [[lane('edgeKinds', 2, 4*a+d) for d in range(4)] for a in range(3741)]
assert max(raw) == 3741
assert all(0 <= code < 4**10 for code in representatives)
assert all(0 <= code <= 3741 for row in destinations for code in row)
assert all((destinations[a][d] == 0) == (kinds[a][d] == 3)
           for a in range(3741) for d in range(4))

steps = ((1, 0), (0, 1), (-1, 0), (0, -1))
raw_geometry = {}
counts_by_depth = [0]*11


def bond(x, y):
    return tuple(sorted((x, y)))


def generate(depth, code, vertices, used):
    counts_by_depth[depth] += 1
    if depth == 10:
        endpoint = vertices[-1]
        revisit = endpoint in vertices[:-1]
        last = code % 4
        allowed = []
        departure_kinds = []
        for d, (dx, dy) in enumerate(steps):
            next_vertex = (endpoint[0] + dx, endpoint[1] + dy)
            allowed.append(d != (last + 2) % 4 and bond(endpoint, next_vertex) not in used)
            departure_kinds.append(2 if revisit else (0 if d == last else 1))
        assert raw[code] < 3741, ('raw coverage', code, raw[code])
        raw_geometry[code] = (tuple(allowed), tuple(departure_kinds), last)
        return
    endpoint = vertices[-1]
    for d, (dx, dy) in enumerate(steps):
        next_vertex = (endpoint[0] + dx, endpoint[1] + dy)
        next_bond = bond(endpoint, next_vertex)
        if next_bond not in used:
            used.add(next_bond)
            vertices.append(next_vertex)
            generate(depth + 1, 4*code + d, vertices, used)
            vertices.pop()
            used.remove(next_bond)


generate(0, 0, [(0, 0)], set())
assert counts_by_depth[1:] == [4, 12, 36, 108, 316, 916, 2628, 7500, 21268, 60092]
assert all((value < 3741) == (code in raw_geometry) for code, value in enumerate(raw))
for a, code in enumerate(representatives):
    assert code in raw_geometry and raw[code] == a, ('representative', a, code)

transition_comparisons = 0
nonrevisit_arrivals = 0
for code, (allowed, departure_kinds, last) in raw_geometry.items():
    a = raw[code]
    rep_allowed, rep_kinds, rep_last = raw_geometry[representatives[a]]
    assert allowed == rep_allowed, ('class admissibility', code, a)
    # Paper lemma requests identical kind even for directions not admitted.
    assert departure_kinds == rep_kinds, ('class kinds', code, a)
    for d in range(4):
        assert allowed[d] == (destinations[a][d] != 0), ('stored admissibility', code, a, d)
        if allowed[d]:
            successor = (code % (4**9))*4 + d
            assert successor in raw_geometry
            assert kinds[a][d] == departure_kinds[d], ('stored kind', code, a, d)
            assert destinations[a][d] - 1 == raw[successor], ('stored successor', code, a, d)
            transition_comparisons += 1
            if departure_kinds[d] != 2:
                assert last == rep_last, ('nonrevisit arrival', code, a, d)
                nonrevisit_arrivals += 1

edge_counts = Counter(kinds[a][d] for a in range(3741) for d in range(4) if destinations[a][d])
assert [edge_counts[k] for k in range(3)] == [2516, 5032, 1872]

result = {
    'literal_count': len(constants),
    'packed_bit_lengths': {name: value.bit_length() for name, value in packed.items()},
    'counts_by_depth': counts_by_depth,
    'raw_entries': len(raw),
    'raw_valid': len(raw_geometry),
    'raw_sentinel': raw.count(3741),
    'representatives_checked': len(representatives),
    'admitted_raw_transitions_checked': transition_comparisons,
    'nonrevisit_arrivals_checked': nonrevisit_arrivals,
    'quotient_edge_counts': [edge_counts[k] for k in range(3)],
    'target_chunks': {},
}
for i in range(140, 145):
    name = f'rawClass_{i}'
    lower_bit = leaf_offsets['rawClass'][name]
    upper_bit = lower_bit + 16384 - 1
    first_code, last_code = lower_bit // 12, upper_bit // 12
    touched_codes = list(range(first_code, last_code + 1))
    valid = [code for code in touched_codes if code in raw_geometry]
    wholly_contained = [code for code in touched_codes if lower_bit <= 12*code and 12*code + 11 <= upper_bit]
    boundary = [code for code in touched_codes if code not in wholly_contained]
    result['target_chunks'][name] = {
        'source_line': source_lines[name],
        'bit_length': constants[name].bit_length(),
        'bit_interval_inclusive': [lower_bit, upper_bit],
        'code_interval_inclusive': [first_code, last_code],
        'wholly_contained_lanes': len(wholly_contained),
        'boundary_codes_and_values': [(code, raw[code]) for code in boundary],
        'valid_raw_codes': len(valid),
        'sentinel_raw_codes': sum(raw[code] == 3741 for code in touched_codes),
        'classes_used': sorted({raw[code] for code in valid}),
        'first_valid_code_class_pairs': [(code, raw[code]) for code in valid[:5]],
        'last_valid_code_class_pairs': [(code, raw[code]) for code in valid[-5:]],
    }

path = HERE / 'audit_results.json'
path.write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
