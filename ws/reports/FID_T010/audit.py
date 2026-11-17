"""Read-only reconstruction of the memory-ten table from the paper's rules."""

import ast
from collections import Counter
from pathlib import Path
import re


SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
text = SOURCE.read_text()
literal_matches = list(re.finditer(
    r'^private noncomputable def (\w+) : ℕ := 0x([0-9a-f]+)$', text, re.M))
literals = {m[1]: int(m[2], 16) for m in literal_matches}
print('Parsed every literal:', len(literals), flush=True)


def expression(name):
    rhs = re.search(r'^noncomputable def ' + name + r' : ℕ := (.*)$', text, re.M)[1]
    return ast.parse(rhs.replace('<<<', '<<'), mode='eval').body


def evaluate(node):
    if isinstance(node, ast.Name):
        return literals[node.id]
    if isinstance(node, ast.Constant):
        assert isinstance(node.value, int) and node.value >= 0
        return node.value
    assert isinstance(node, ast.BinOp)
    left, right = evaluate(node.left), evaluate(node.right)
    if isinstance(node.op, ast.Add):
        return left + right
    assert isinstance(node.op, ast.LShift)
    return left << right


def positions(node, shift=0):
    if isinstance(node, ast.Name):
        return [(node.id, shift)]
    assert isinstance(node, ast.BinOp)
    if isinstance(node.op, ast.Add):
        return positions(node.left, shift) + positions(node.right, shift)
    assert isinstance(node.op, ast.LShift)
    return positions(node.left, shift + evaluate(node.right))


tables = {n: evaluate(expression(n)) for n in
          ('rawClass', 'representatives', 'destinations', 'edgeKinds')}
raw_positions = dict(positions(expression('rawClass')))
ordered = sorted(raw_positions.items(), key=lambda p: p[1])
assert len(ordered) == 768
for (name, off), (_, next_off) in zip(ordered, ordered[1:]):
    assert literals[name] < (1 << (next_off - off))
assert tables['rawClass'] < (1 << (12 * 4**10))
print('Parsed every packing expression; chunks have no overlap or carry.', flush=True)


def lanes(name, width, count):
    # Extract from little-endian bytes, without repeatedly shifting a 1.5 MB integer.
    packed = tables[name].to_bytes((width * count + 7) // 8, 'little')
    mask = (1 << width) - 1
    result = []
    for i in range(count):
        bit = width * i
        byte, rem = divmod(bit, 8)
        result.append((int.from_bytes(packed[byte:byte + (width + rem + 7)//8],
                                      'little') >> rem) & mask)
    return result


raw_map = lanes('rawClass', 12, 4**10)
representatives = lanes('representatives', 20, 3741)
destinations = lanes('destinations', 12, 3741 * 4)
edge_kinds = lanes('edgeKinds', 2, 3741 * 4)

STEPS = ((1, 0), (0, 1), (-1, 0), (0, -1))
counts = [0] * 11
raw_codes = []


def generate(depth, code, z, used):
    counts[depth] += 1
    if depth == 10:
        raw_codes.append(code)
        return
    for d, (dx, dy) in enumerate(STEPS):
        zz = z[0] + dx, z[1] + dy
        bond = tuple(sorted((z, zz)))
        if bond in used:
            continue
        used.add(bond)
        generate(depth + 1, 4 * code + d, zz, used)
        used.remove(bond)


generate(0, 0, (0, 0), set())
print('Independent raw counts:', counts[1:], flush=True)
assert counts[1:] == [4, 12, 36, 108, 316, 916, 2628, 7500, 21268, 60092]
raw_set = set(raw_codes)
assert len(raw_set) == len(raw_codes)
assert raw_codes == sorted(raw_codes)


def decode(code):
    return tuple((code >> (2 * (9 - i))) & 3 for i in range(10))


def describe(code):
    word = decode(code)
    z = (0, 0)
    earlier = set()
    used = set()
    for d in word:
        earlier.add(z)
        dx, dy = STEPS[d]
        zz = z[0] + dx, z[1] + dy
        used.add(tuple(sorted((z, zz))))
        z = zz
    revisit = z in earlier
    kinds = tuple(2 if revisit else (0 if d == word[-1] else 1) for d in range(4))
    successors = []
    for d, (dx, dy) in enumerate(STEPS):
        zz = z[0] + dx, z[1] + dy
        allowed = d != (word[-1] + 2) % 4 and tuple(sorted((z, zz))) not in used
        successors.append(((code % 4**9) * 4 + d) if allowed else None)
    arrival = word[-1] if any(s is not None and kinds[d] != 2
                             for d, s in enumerate(successors)) else None
    return kinds, tuple(successors), arrival


descriptions = [describe(code) for code in raw_codes]
index = {c: i for i, c in enumerate(raw_codes)}
successor_indices = [tuple(index[c] if c is not None else -1 for c in ss)
                     for _, ss, _ in descriptions]
initial = [(kinds, tuple(c is not None for c in ss), arrival)
           for kinds, ss, arrival in descriptions]


def classify(signatures):
    classes = {}
    return [classes.setdefault(sig, len(classes)) for sig in signatures], len(classes)


# Use all four raw kinds, including forbidden directions, as in the paper's lemma.
partition, q = classify(initial)
print('Initial behavior classes:', q, flush=True)
rounds = 0
while True:
    new_partition, new_q = classify(
        (partition[i], tuple(partition[j] if j >= 0 else -1 for j in ss))
        for i, ss in enumerate(successor_indices))
    rounds += 1
    print('Refinement round:', rounds, 'classes:', new_q, flush=True)
    if new_q == q:
        partition = new_partition
        break
    partition, q = new_partition, new_q

assert new_q == 3741
assert len(set(representatives)) == 3741
assert all(c in raw_set for c in representatives)
label_by_behavior = {}
for a, c in enumerate(representatives):
    behavior = partition[index[c]]
    assert behavior not in label_by_behavior
    label_by_behavior[behavior] = a
assert len(label_by_behavior) == 3741
expected_map = [3741] * 4**10
for i, code in enumerate(raw_codes):
    expected_map[code] = label_by_behavior[partition[i]]

coverage_errors = [c for c, a in enumerate(raw_map)
                   if a > 3741 or ((a < 3741) != (c in raw_set))]
map_errors = [c for c in range(4**10) if raw_map[c] != expected_map[c]]
print('All-code coverage errors:', len(coverage_errors), coverage_errors[:10], flush=True)
print('All-code behavior/representative-label errors:', len(map_errors), map_errors[:10], flush=True)

row_errors = []
counts_by_kind = Counter()
for a, c in enumerate(representatives):
    kinds, ss, _ = descriptions[index[c]]
    for d in range(4):
        at = 4 * a + d
        expected_destination = 0 if ss[d] is None else expected_map[ss[d]] + 1
        expected_kind = 3 if ss[d] is None else kinds[d]
        if destinations[at] != expected_destination or edge_kinds[at] != expected_kind:
            row_errors.append((a, d, destinations[at], expected_destination,
                               edge_kinds[at], expected_kind))
        if ss[d] is not None:
            counts_by_kind[kinds[d]] += 1
print('Stored row errors:', len(row_errors), row_errors[:10], flush=True)
print('Representative edge counts (straight/turn/revisit):', dict(counts_by_kind), flush=True)
assert counts_by_kind == {0: 2516, 1: 5032, 2: 1872}

# Construct all expected lanes independently; reverse hex concatenation is exact base 2^12.
expected_packed = int(''.join(f'{a:03x}' for a in reversed(expected_map)), 16)
for k in range(15, 20):
    name = f'rawClass_{k}'
    lo = raw_positions[name]
    width = 16384
    first, last = lo // 12, (lo + width - 1) // 12
    expected_literal = (expected_packed >> lo) & ((1 << width) - 1)
    differing = [c for c in range(first, last + 1) if raw_map[c] != expected_map[c]]
    full_first = (lo + 11) // 12
    full_stop = (lo + width) // 12
    raw_touching = sum(c in raw_set for c in range(first, last + 1))
    raw_complete = sum(c in raw_set for c in range(full_first, full_stop))
    print(name, {
        'source_line': next(text[:m.start()].count('\n') + 1 for m in literal_matches if m[1] == name),
        'bit_offset': lo, 'bit_width': width, 'offset_mod_12': lo % 12,
        'touching_codes': [first, last], 'touching_raw': raw_touching,
        'complete_codes': [full_first, full_stop - 1], 'complete_raw': raw_complete,
        'literal_matches_independent_reconstruction': literals[name] == expected_literal,
        'touching_lane_errors': differing,
    }, flush=True)
    examples = [c for c in range(full_first, full_stop) if c in raw_set]
    if examples:
        c = examples[len(examples)//2]
        print('  example:', c, ''.join('ENWS'[d] for d in decode(c)),
              'class', raw_map[c], 'representative', representatives[raw_map[c]], flush=True)

assert not coverage_errors and not map_errors and not row_errors
print('AUDIT PASSED', flush=True)
