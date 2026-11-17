"""Read-only reconstruction of the memory-ten data and the paper's finite checks."""

import ast
import hashlib
import json
import re
from collections import Counter
from pathlib import Path


ROOT = Path('/home/ubuntu/aklt/review/FID_T')
SOURCE = ROOT / 'lean/AKLT/Defs/Automaton10Data.lean'
text = SOURCE.read_text()
literals = {
    name: int(value, 16)
    for name, value in re.findall(r'def (\w+) : ℕ := 0x([0-9a-f]+)', text)
}
directions = ((1, 0), (0, 1), (-1, 0), (0, -1))
errors = []


def check(condition, detail):
    if not condition:
        errors.append(detail)


def assembly(name):
    expr = re.search(r'^noncomputable def ' + name + r' : ℕ := (.*)$', text, re.M)[1]
    tree = ast.parse(expr.replace('<<<', '<<'), mode='eval').body
    leaves = []

    def evaluate(node, offset=0):
        if isinstance(node, ast.Name):
            leaves.append((node.id, offset))
            return literals[node.id]
        if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add):
            return evaluate(node.left, offset) + evaluate(node.right, offset)
        if isinstance(node, ast.BinOp) and isinstance(node.op, ast.LShift):
            return evaluate(node.left, offset + node.right.value) << node.right.value
        raise ValueError(ast.dump(node))

    packed = evaluate(tree)
    ordered = sorted(leaves, key=lambda item: item[1])
    check(len({n for n, o in leaves}) == len(leaves), (name, 'repeated leaf'))
    for (n, o), (_, next_offset) in zip(ordered, ordered[1:]):
        check(literals[n].bit_length() <= next_offset - o, (name, n, 'overlap'))
    data = packed.to_bytes((packed.bit_length() + 7) // 8 + 4, 'little')

    def lane(width, index):
        bit = width * index
        start, shift = divmod(bit, 8)
        length = (width + shift + 7) // 8
        return (int.from_bytes(data[start:start + length], 'little') >> shift) % (1 << width)

    return lane, dict(leaves)


raw_lane, offsets = assembly('rawClass')
rep_lane, _ = assembly('representatives')
dest_lane, _ = assembly('destinations')
kind_lane, _ = assembly('edgeKinds')
raw_class = [raw_lane(12, c) for c in range(4 ** 10)]


def bond(a, b):
    return tuple(sorted((a, b)))


raw = {}
counts = Counter()


def generate(code=0, word=(), point=(0, 0), used=frozenset(), departed=frozenset()):
    counts[len(word)] += 1
    if len(word) == 10:
        raw[code] = (word, point, used, departed)
        return
    for d, delta in enumerate(directions):
        new_point = (point[0] + delta[0], point[1] + delta[1])
        edge = bond(point, new_point)
        if edge not in used:
            generate(code * 4 + d, word + (d,), new_point,
                     used | {edge}, departed | {point})


generate()
check([counts[i] for i in range(1, 11)] ==
      [4, 12, 36, 108, 316, 916, 2628, 7500, 21268, 60092], 'raw counts')

for code, a in enumerate(raw_class):
    check(0 <= a <= 3741 and ((a < 3741) == (code in raw)),
          ('raw coverage', code, a, code in raw))

representatives = [rep_lane(20, a) for a in range(3741)]
for a, code in enumerate(representatives):
    check(code < 4 ** 10 and code in raw, ('representative validity', a, code))
    check(raw_class[code] == a, ('representative class', a, code, raw_class[code]))

edge_counts = Counter()
for a in range(3741):
    for d in range(4):
        destination = dest_lane(12, 4 * a + d)
        kind = kind_lane(2, 4 * a + d)
        check(destination <= 3741 and ((destination == 0) == (kind == 3)),
              ('row encoding', a, d, destination, kind))
        if destination:
            edge_counts[kind] += 1


def actual_kind(state, d):
    word, point, used, departed = state
    return 2 if point in departed else (0 if d == word[-1] else 1)


def actual_allowed(state, d):
    word, point, used, departed = state
    delta = directions[d]
    new_point = (point[0] + delta[0], point[1] + delta[1])
    return d != (word[-1] + 2) % 4 and bond(point, new_point) not in used


for code, state in raw.items():
    a = raw_class[code]
    if a >= 3741:
        continue
    representative = raw.get(representatives[a])
    if representative is None:
        continue
    for d in range(4):
        allowed = actual_allowed(state, d)
        kind = actual_kind(state, d)
        check(allowed == actual_allowed(representative, d),
              ('class admissibility', code, a, d))
        check(kind == actual_kind(representative, d), ('class kind', code, a, d))
        destination = dest_lane(12, 4 * a + d)
        check(allowed == bool(destination), ('stored admissibility', code, a, d))
        if allowed:
            successor = (code % (4 ** 9)) * 4 + d
            check(successor in raw, ('successor validity', code, d, successor))
            check(destination - 1 == raw_class[successor],
                  ('stored successor', code, a, d, destination, raw_class[successor]))
            check(kind_lane(2, 4 * a + d) == kind, ('stored kind', code, a, d))
            if kind != 2:
                check(state[0][-1] == representatives[a] % 4, ('class arrival', code, a, d))

check([edge_counts[k] for k in range(3)] == [2516, 5032, 1872], 'quotient edge counts')

assigned = []
for i in range(535, 540):
    name = f'rawClass_{i}'
    offset = offsets[name]
    width = 4 * len(re.search(r'def ' + name + r' : ℕ := 0x([0-9a-f]+)', text)[1])
    low, high = offset // 12, (offset + width - 1) // 12
    valid = [c for c in range(low, high + 1) if c in raw]
    valid_whole = [c for c in valid if offset <= 12 * c and 12 * c + 12 <= offset + width]
    invalid = high - low + 1 - len(valid)
    # Check every bit of this literal against the reconstructed complete lanes,
    # including lanes split at chunk boundaries.
    expected = sum(raw_class[c] << (12 * (c - low)) for c in range(low, high + 1))
    expected = (expected >> (offset - 12 * low)) % (1 << width)
    check(expected == literals[name], ('chunk reconstruction', name))
    assigned.append({
        'name': name,
        'source_line': text[:text.index('private noncomputable def ' + name + ' ')].count('\n') + 1,
        'offset': offset,
        'bits': width,
        'touched_codes': [low, high],
        'touched_raw': len(valid),
        'touched_nonraw': invalid,
        'whole_raw_lanes': len(valid_whole),
        'distinct_valid_classes': len({raw_class[c] for c in valid}),
        'first_raw': valid[0] if valid else None,
        'last_raw': valid[-1] if valid else None,
        'literal_sha256': hashlib.sha256(literals[name].to_bytes(width // 8, 'big')).hexdigest(),
    })

result = {
    'source_sha256': hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
    'raw_counts': [counts[i] for i in range(1, 11)],
    'coverage_checked': len(raw_class),
    'raw_states_checked': len(raw),
    'raw_directions_checked': 4 * len(raw),
    'classes': len(representatives),
    'edge_counts_straight_turn_revisit': [edge_counts[k] for k in range(3)],
    'assigned': assigned,
    'error_count': len(errors),
    'errors': errors[:30],
}
print(json.dumps(result, indent=2))
Path(__file__).with_name('audit_results.json').write_text(json.dumps(result, indent=2) + '\n')
