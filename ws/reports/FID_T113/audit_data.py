"""Independent integer/lattice audit of the supplied Lean literal data.

Reads only the supplied Lean input. No Lean process or archived data is used.
"""

from collections import Counter
from pathlib import Path
import json
import re


SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
text = SOURCE.read_text()
literals = {
    name: int(value, 16)
    for name, value in re.findall(
        r'^private noncomputable def (\w+) : ℕ := 0x([0-9a-f]+)$',
        text, re.M,
    )
}


def assembly(name, precedence):
    body = re.search(rf'^noncomputable def {name} : ℕ := (.*)$', text, re.M)[1]
    tokens = re.findall(r'\w+|<<<|[()+]', body)
    assert ''.join(tokens) == re.sub(r'\s+', '', body)
    pos = 0

    def expr(minimum=0):
        nonlocal pos
        token = tokens[pos]
        pos += 1
        if token == '(':
            node = expr()
            assert tokens[pos] == ')'
            pos += 1
        else:
            node = token
        while pos < len(tokens) and tokens[pos] in precedence:
            op = tokens[pos]
            priority = precedence[op]
            if priority < minimum:
                break
            pos += 1
            node = (op, node, expr(priority + 1))
        return node

    tree = expr()
    assert pos == len(tokens)
    return tree


def eval_tree(tree):
    if isinstance(tree, str):
        return int(tree) if tree.isdecimal() else literals[tree]
    op, left, right = tree
    a, b = eval_tree(left), eval_tree(right)
    return a + b if op == '+' else a << b


def offsets(tree, offset=0):
    if isinstance(tree, str):
        assert tree in literals
        return [(tree, offset)]
    op, left, right = tree
    if op == '<<<':
        return offsets(left, offset + eval_tree(right))
    return offsets(left, offset) + offsets(right, offset)


trees = {}
packed = {}
for name in ('rawClass', 'representatives', 'destinations', 'edgeKinds'):
    variants = [assembly(name, p) for p in (
        {'+': 1, '<<<': 1}, {'+': 2, '<<<': 1}, {'+': 1, '<<<': 2},
    )]
    assert variants[0] == variants[1] == variants[2]
    trees[name] = variants[0]
    packed[name] = eval_tree(variants[0])

raw_offsets = dict(offsets(trees['rawClass']))
assert len(raw_offsets) == 768
assert set(raw_offsets) == {f'rawClass_{i}' for i in range(768)}
for i in range(768):
    # The whole packed integer omits its leading zero hexadecimal digit;
    # high-to-low splitting therefore leaves the final low block 4 bits short.
    expected_offset = (767-i)*16384-4 if i < 767 else 0
    assert raw_offsets[f'rawClass_{i}'] == expected_offset
    assert 0 <= literals[f'rawClass_{i}'] < 2**16384
assert literals['rawClass_767'] < 2**16380

total_codes = 4**10
assert packed['rawClass'] < 2**(12*total_codes)
raw_bytes = packed['rawClass'].to_bytes(12*total_codes//8, 'little')
raw_class = []
for i in range(0, len(raw_bytes), 3):
    a, b, c = raw_bytes[i:i+3]
    raw_class.extend((a + ((b & 15) << 8), (b >> 4) + (c << 4)))
assert len(raw_class) == total_codes


def lanes(name, width, count):
    value = packed[name]
    assert value < 2**(width*count)
    return [(value >> (width*i)) % 2**width for i in range(count)]


representatives = lanes('representatives', 20, 3741)
destinations = lanes('destinations', 12, 3741*4)
kinds = lanes('edgeKinds', 2, 3741*4)
assert all(0 <= a <= 3741 for a in raw_class)
assert all(0 <= r < total_codes for r in representatives)
assert all(0 <= a <= 3741 for a in destinations)
assert all((a == 0) == (k == 3) for a, k in zip(destinations, kinds))

STEPS = ((1, 0), (0, 1), (-1, 0), (0, -1))


def edge(a, b):
    return tuple(sorted((a, b)))


# Enumerate the paper's prefix recursion from the empty word. Absolute
# directions are tried in E,N,W,S order, with no virtual incoming bond.
counts = [0]*11
windows = {}


def generate(directions, vertices, bonds, code):
    n = len(directions)
    counts[n] += 1
    if n == 10:
        windows[code] = (directions, vertices, bonds)
        return
    x, y = vertices[-1]
    for d, (dx, dy) in enumerate(STEPS):
        target = (x+dx, y+dy)
        bond = edge((x, y), target)
        if bond not in bonds:
            generate(directions+(d,), vertices+(target,), bonds | {bond}, 4*code+d)


generate((), ((0, 0),), frozenset(), 0)
assert counts == [1, 4, 12, 36, 108, 316, 916, 2628, 7500, 21268, 60092]
coverage_errors = [c for c, a in enumerate(raw_class) if (a < 3741) != (c in windows)]
assert not coverage_errors, coverage_errors[:10]
assert len(set(representatives)) == 3741
for a, code in enumerate(representatives):
    assert code in windows and raw_class[code] == a


def row(code):
    directions, vertices, bonds = windows[code]
    x, y = vertices[-1]
    revisit = vertices[-1] in vertices[:-1]
    result = []
    for d, (dx, dy) in enumerate(STEPS):
        admissible = d != (directions[-1]+2) % 4 and edge((x, y), (x+dx, y+dy)) not in bonds
        kind = 2 if revisit else (0 if d == directions[-1] else 1)
        successor = (code % 4**9)*4+d
        result.append((admissible, kind, successor))
    return result


row_errors = []
class_sizes = Counter()
for code, (directions, vertices, bonds) in windows.items():
    a = raw_class[code]
    class_sizes[a] += 1
    rep = representatives[a]
    representative_row = row(rep)
    for d, (admissible, kind, successor) in enumerate(row(code)):
        j = a*4+d
        if admissible != (destinations[j] != 0):
            row_errors.append((code, d, 'admissibility'))
        # Compare kind with the representative even on forbidden directions,
        # as required by the paper's CompatibleProjection formulation.
        if kind != representative_row[d][1]:
            row_errors.append((code, d, 'representative kind'))
        if admissible:
            if successor not in windows:
                row_errors.append((code, d, 'raw successor'))
            if kinds[j] != kind:
                row_errors.append((code, d, 'stored kind'))
            if destinations[j]-1 != raw_class[successor]:
                row_errors.append((code, d, 'successor class'))
            if kind != 2 and directions[-1] != windows[rep][0][-1]:
                row_errors.append((code, d, 'nonrevisit arrival'))
assert not row_errors, row_errors[:10]
edge_counts = Counter(k for dest, k in zip(destinations, kinds) if dest != 0)
assert edge_counts == {0: 2516, 1: 5032, 2: 1872}

# Recompute every reviewed literal from the independently generated validity
# predicate, retaining the verified supplied class numbers on valid words.
# Fragments can split a 12-bit lane; do not assume chunk/lane alignment.
fragment_results = []
for i in range(530, 535):
    name = f'rawClass_{i}'
    lo = raw_offsets[name]
    hi = lo + 16384
    first, last = lo//12, (hi-1)//12
    rebuilt = 0
    valid = []
    invalid = []
    for code in range(first, last+1):
        a = raw_class[code] if code in windows else 3741
        start, stop = max(lo, 12*code), min(hi, 12*code+12)
        part = (a >> (start-12*code)) % 2**(stop-start)
        rebuilt += part << (start-lo)
        (valid if code in windows else invalid).append(code)
    assert rebuilt == literals[name]
    fragment_results.append({
        'declaration': name,
        'source_line': 15+2*i,
        'bit_start': lo,
        'bit_end_exclusive': hi,
        'first_code': first,
        'last_code': last,
        'intersecting_lanes': last-first+1,
        'valid_lanes': len(valid),
        'invalid_lanes': len(invalid),
        'distinct_valid_classes': len({raw_class[c] for c in valid}),
        'start_within_first_lane': lo % 12,
        'end_within_last_lane_exclusive': hi % 12,
        'literal_reconstruction': 'PASS',
    })

output = {
    'raw_codes': total_codes,
    'generated_prefix_counts': counts,
    'raw_windows': len(windows),
    'invalid_codes': total_codes-len(windows),
    'classes': len(class_sizes),
    'coverage_errors': len(coverage_errors),
    'row_errors': len(row_errors),
    'straight_turn_revisit_edge_counts': [edge_counts[i] for i in range(3)],
    'raw_chunk_assembly': '767 disjoint 16384-bit blocks and one low 16380-bit block, high to low',
    'fragments': fragment_results,
}
print(json.dumps(output, indent=2))
