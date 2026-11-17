"""Read-only reconstruction checks for the five assigned literal chunks."""
from pathlib import Path
import hashlib
import json
import re

BASE = Path('/home/ubuntu/aklt/review/FID_T/lean')
source = (BASE / 'AKLT/Defs/Automaton10Data.lean').read_text()
literal_re = r'private noncomputable def (\w+) : ℕ := (0x[0-9a-f]+)'
literals = {name: int(value, 16) for name, value in re.findall(literal_re, source)}


def parse(expression):
    tokens = re.findall(r'<<<|[()+]|\w+', expression)
    cursor = 0

    def atom():
        nonlocal cursor
        token = tokens[cursor]
        cursor += 1
        if token == '(':
            result = expr()
            assert tokens[cursor] == ')'
            cursor += 1
            return result
        return int(token) if token.isdecimal() else token

    def expr():
        nonlocal cursor
        result = atom()
        while cursor < len(tokens) and tokens[cursor] != ')':
            operator = tokens[cursor]
            cursor += 1
            assert operator in ('+', '<<<')
            result = (operator, result, atom())
        return result

    result = expr()
    assert cursor == len(tokens)
    return result


def evaluate(tree):
    if isinstance(tree, int):
        return tree
    if isinstance(tree, str):
        return literals[tree]
    op, left, right = tree
    return (evaluate(left) + evaluate(right) if op == '+'
            else evaluate(left) << evaluate(right))


def leaf_offsets(tree, offset=0):
    if isinstance(tree, str):
        return [(tree, offset)]
    op, left, right = tree
    if op == '<<<':
        return leaf_offsets(left, offset + evaluate(right))
    return leaf_offsets(left, offset) + leaf_offsets(right, offset)


def table(name, width, length):
    expression = re.search(r'^noncomputable def ' + name + r' : ℕ := (.+)$',
                           source, re.M)[1]
    tree = parse(expression)
    value = evaluate(tree)
    offsets = leaf_offsets(tree)
    # Check every literal occupies a disjoint range in the concatenation.
    ordered = sorted(offsets, key=lambda item: item[1])
    assert ordered[0][1] == 0
    for (prev, start), (_, end) in zip(ordered, ordered[1:]):
        assert literals[prev].bit_length() <= end - start
    assert value.bit_length() <= width * length
    blob = value.to_bytes((width * length + 7) // 8, 'little')
    mask = (1 << width) - 1
    lanes = []
    for index in range(length):
        bit = width * index
        lane = (int.from_bytes(blob[bit // 8:(bit + width + 7) // 8], 'little')
                >> (bit % 8)) & mask
        lanes.append(lane)
    return lanes, offsets


N = 4**10
classes, offsets = table('rawClass', 12, N)
representatives, _ = table('representatives', 20, 3741)
destinations, _ = table('destinations', 12, 4 * 3741)
kinds, _ = table('edgeKinds', 2, 4 * 3741)
assert max(classes) <= 3741
assert max(representatives) < N
assert max(destinations) <= 3741
assert all((destination == 0) == (kind == 3)
           for destination, kind in zip(destinations, kinds))

steps = ((1, 0), (0, 1), (-1, 0), (0, -1))


def bond(a, b):
    return tuple(sorted((a, b)))


def path(code):
    word = tuple((code >> (2 * (9-i))) & 3 for i in range(10))
    vertices = [(0, 0)]
    bonds = set()
    for d in word:
        x, y = vertices[-1]
        dx, dy = steps[d]
        nxt = (x + dx, y + dy)
        edge = bond(vertices[-1], nxt)
        assert edge not in bonds
        bonds.add(edge)
        vertices.append(nxt)
    return word, vertices, bonds


def row(word, vertices, bonds):
    x, y = vertices[-1]
    revisit = vertices[-1] in vertices[:-1]
    result = []
    for d, (dx, dy) in enumerate(steps):
        allowed = d != (word[-1] + 2) % 4 and bond((x, y), (x+dx, y+dy)) not in bonds
        kind = 2 if revisit else 0 if d == word[-1] else 1
        result.append((allowed, kind))
    return result


rep_rows = []
rep_arrivals = []
for a, code in enumerate(representatives):
    assert classes[code] == a, (a, code, classes[code])
    w, vertices, bonds = path(code)
    rep_rows.append(row(w, vertices, bonds))
    rep_arrivals.append(w[-1])

counts = [0] * 11
raw_codes = []
raw_set = set()
checks = dict(admissibility=0, kind=0, successor=0, arrival=0)


def generate(word=(), vertices=((0, 0),), bonds=frozenset(), code=0):
    depth = len(word)
    counts[depth] += 1
    if depth == 10:
        raw_codes.append(code)
        raw_set.add(code)
        a = classes[code]
        assert a < 3741, ('raw marked invalid', code, a)
        for d, (allowed, kind) in enumerate(row(word, vertices, bonds)):
            checks['admissibility'] += 1
            assert allowed == (destinations[4*a+d] != 0), (code, a, d, 'allowed')
            # Paper lemma requires matching kind even on inadmissible directions.
            checks['kind'] += 1
            assert (allowed, kind) == rep_rows[a][d], (code, a, d, 'representative')
            if allowed:
                assert kind == kinds[4*a+d], (code, a, d, 'stored kind')
                successor = ((code % (4**9)) * 4) + d
                checks['successor'] += 1
                assert classes[successor] < 3741
                assert classes[successor] == destinations[4*a+d] - 1, (code, a, d, 'successor')
                if kind != 2:
                    checks['arrival'] += 1
                    assert word[-1] == rep_arrivals[a], (code, a, 'arrival')
        return
    x, y = vertices[-1]
    for d, (dx, dy) in enumerate(steps):
        nxt = (x+dx, y+dy)
        edge = bond(vertices[-1], nxt)
        if edge not in bonds:
            generate(word + (d,), vertices + (nxt,), bonds | {edge}, code*4+d)


generate()
assert counts[1:] == [4, 12, 36, 108, 316, 916, 2628, 7500, 21268, 60092]
assert raw_codes == sorted(raw_codes)
assert all((value < 3741) == (code in raw_set) for code, value in enumerate(classes))
edge_counts = [sum(destination != 0 and kind == k
                   for destination, kind in zip(destinations, kinds))
               for k in range(3)]
assert edge_counts == [2516, 5032, 1872]

details = []
for j in range(235, 240):
    name = f'rawClass_{j}'
    start = dict(offsets)[name]
    # All five are full 16,384-bit chunks; some lanes straddle chunk boundaries.
    end = start + 16384
    low_code = start // 12
    high_code = (end - 1) // 12
    affected = range(low_code, high_code + 1)
    valid = [code for code in affected if code in raw_set]
    details.append(dict(name=name, lean_line=15+2*j,
                        bit_start=start, bit_end_exclusive=end,
                        low_code=low_code, high_code=high_code,
                        lane_count=len(affected), raw_count=len(valid),
                        invalid_count=len(affected)-len(valid),
                        distinct_classes=len({classes[code] for code in valid}),
                        first_raw_code=valid[0] if valid else None,
                        first_raw_class=classes[valid[0]] if valid else None,
                        start_mod_12=start % 12, end_mod_12=end % 12))

# Reconstruct the canonical text format described by the paper. This is not
# compared to any external archive; only the Lean-embedded SHA-256 comment.
lines = ['60092 3741']
lines.extend(f'{code} {classes[code]}' for code in raw_codes)
for a in range(3741):
    successor = [destinations[4*a+d]-1 for d in range(4)]
    kind = [kinds[4*a+d] if destinations[4*a+d] else -1 for d in range(4)]
    lines.append(' '.join(map(str, [representatives[a], *successor, *kind])))
digest = hashlib.sha256(('\n'.join(lines)+'\n').encode()).hexdigest()
expected_digest = re.search(r'Archive SHA-256: ([a-f0-9]+)', source)[1]

summary = dict(raw_counts=counts[1:], checks=checks, edge_counts=edge_counts,
               reconstructed_sha256=digest, comment_sha256=expected_digest,
               digest_matches=(digest == expected_digest), declarations=details,
               all_checks_pass=True)
print(json.dumps(summary, indent=2))
