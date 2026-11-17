"""Read-only numerical audit of the Lean literals against the paper's recursion."""

import ast
from array import array
from collections import Counter
from pathlib import Path
import re

SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
values = {}
locations = {}


def evaluate(node):
    if isinstance(node, ast.Constant) and isinstance(node.value, int):
        return node.value
    if isinstance(node, ast.Name):
        return values[node.id]
    if isinstance(node, ast.BinOp):
        left, right = evaluate(node.left), evaluate(node.right)
        if isinstance(node.op, ast.Add):
            return left + right
        if isinstance(node.op, ast.LShift):
            assert isinstance(node.right, ast.Constant)
            return left << right
    raise ValueError(ast.dump(node))


for line_number, line in enumerate(SOURCE.read_text().splitlines(), 1):
    match = re.fullmatch(r'(?:private )?noncomputable def (\w+) : ℕ := (.+)', line)
    if match:
        name, expression = match.groups()
        # Each shift operation in the source is explicitly parenthesized.
        values[name] = evaluate(ast.parse(expression.replace('<<<', '<<'), mode='eval').body)
        locations[name] = line_number


def unpack(name, width, count):
    packed = values[name]
    assert packed >> (width * count) == 0, name
    data = packed.to_bytes((width * count + 7) // 8, 'little')
    result = array('I' if width > 16 else 'H')
    buffer = bits = 0
    mask = (1 << width) - 1
    for byte in data:
        buffer |= byte << bits
        bits += 8
        while bits >= width and len(result) < count:
            result.append(buffer & mask)
            buffer >>= width
            bits -= width
    assert len(result) == count
    print(f'{name}: source line {locations[name]}, {count} lanes, width {width}, '
          f'packed bit length {packed.bit_length()}, range {min(result)}..{max(result)}')
    return result


Q = 3741
MEMORY = 10
WORDS = 4 ** MEMORY
raw = unpack('rawClass', 12, WORDS)
representatives = unpack('representatives', 20, Q)
destinations = unpack('destinations', 12, Q * 4)
kinds = unpack('edgeKinds', 2, Q * 4)
assert max(raw) == Q
assert max(representatives) < WORDS
assert max(destinations) <= Q
for destination, kind in zip(destinations, kinds):
    assert (destination == 0) == (kind == 3)
    assert destination == 0 or kind < 3

steps = ((1, 0), (0, 1), (-1, 0), (0, -1))
counts = Counter()
raw_codes = set()
class_members = Counter()
class_final_directions = [set() for _ in range(Q)]
class_raw_kinds = [None for _ in range(Q)]
checks = Counter()


def bond(x, y):
    return (x, y) if x < y else (y, x)


def visit(code, directions, vertices, used):
    length = len(directions)
    counts[length] += 1
    x, y = vertices[-1]
    if length < MEMORY:
        for d, (dx, dy) in enumerate(steps):
            new_vertex = (x + dx, y + dy)
            new_bond = bond(vertices[-1], new_vertex)
            if new_bond not in used:
                used.add(new_bond)
                directions.append(d)
                vertices.append(new_vertex)
                visit(code * 4 + d, directions, vertices, used)
                vertices.pop()
                directions.pop()
                used.remove(new_bond)
        return

    assert code not in raw_codes
    raw_codes.add(code)
    a = raw[code]
    assert a < Q, ('raw coverage', code, a)
    class_members[a] += 1
    last = directions[-1]
    class_final_directions[a].add(last)
    revisit = vertices[-1] in vertices[:-1]
    raw_kinds = tuple(2 if revisit else (0 if d == last else 1) for d in range(4))
    if class_raw_kinds[a] is None:
        class_raw_kinds[a] = raw_kinds
    assert class_raw_kinds[a] == raw_kinds, ('raw kind compatibility', code, a)
    checks['raw kind compatibility (all directions)'] += 4
    for d, (dx, dy) in enumerate(steps):
        expected_allowed = (d != (last + 2) % 4 and
                            bond(vertices[-1], (x + dx, y + dy)) not in used)
        index = a * 4 + d
        actual_allowed = destinations[index] != 0
        assert actual_allowed == expected_allowed, ('admissibility', code, a, d)
        checks['admissibility'] += 1
        if expected_allowed:
            expected_kind = 2 if revisit else (0 if d == last else 1)
            assert kinds[index] == expected_kind, ('kind', code, a, d)
            checks['kind'] += 1
            successor_code = (code % (4 ** (MEMORY - 1))) * 4 + d
            assert raw[successor_code] < Q
            assert destinations[index] - 1 == raw[successor_code], ('successor', code, a, d)
            checks['successor'] += 1
            if not revisit:
                assert representatives[a] % 4 == last, ('arrival', code, a, d)
                checks['nonrevisit arrival'] += 1


visit(0, [], [(0, 0)], set())
expected_counts = [4, 12, 36, 108, 316, 916, 2628, 7500, 21268, 60092]
assert [counts[j] for j in range(1, MEMORY + 1)] == expected_counts
assert sum(a < Q for a in raw) == len(raw_codes) == 60092
assert sum(a == Q for a in raw) == WORDS - len(raw_codes)
assert len(class_members) == Q
for a, representative in enumerate(representatives):
    assert representative in raw_codes, ('representative trail', a, representative)
    assert raw[representative] == a, ('representative class', a, representative)

edge_counts = Counter(k for d, k in zip(destinations, kinds) if d != 0)
assert edge_counts == Counter({0: 2516, 1: 5032, 2: 1872})
mixed = [a for a in range(Q) if len(class_final_directions[a]) > 1]
assert all(all(k == 2 for d, k in zip(destinations[a*4:a*4+4], kinds[a*4:a*4+4]) if d)
           for a in mixed)
print('Raw recursion counts:', [counts[j] for j in range(1, MEMORY + 1)])
print('Raw/invalid codes:', len(raw_codes), WORDS - len(raw_codes))
print('Representatives are raw and map to their own class:', len(representatives))
print('Exhaustive raw transition comparisons:', dict(checks))
print('Quotient straight/turn/revisit counts:', dict(sorted(edge_counts.items())))
print('Mixed-final-direction classes (all admitted edges revisit):', len(mixed))
print('Kind code lane counts, including inadmissibility:', dict(sorted(Counter(kinds).items())))
print('All finite reconstruction checks passed.')
