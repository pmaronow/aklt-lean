"""Independent, read-only arithmetic and trail-model audit of the supplied data."""
from array import array
from collections import Counter
from pathlib import Path
import json
import re

SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
TEXT = SOURCE.read_text()
LITERALS = {
    name: int(value, 16)
    for name, value in re.findall(
        r'(?:private )?noncomputable def (\w+) : ℕ := (0x[0-9a-fA-F]+)', TEXT
    )
}


def expression(name):
    source = re.search(r'^noncomputable def ' + name + r' : ℕ := (.*)$', TEXT, re.M)[1]
    tokens = re.findall(r'\w+|<<<|[()+]', source)
    assert ''.join(tokens) == re.sub(r'\s+', '', source)
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
        assert token in LITERALS
        return ('leaf', token)

    def expr():
        nonlocal cursor
        result = atom()
        while cursor < len(tokens) and tokens[cursor] != ')':
            operator = tokens[cursor]
            cursor += 1
            if operator == '<<<':
                shift = int(tokens[cursor])
                cursor += 1
                result = ('shift', result, shift)
            else:
                assert operator == '+'
                result = ('add', result, atom())
        return result

    result = expr()
    assert cursor == len(tokens)
    return result


def evaluate(tree):
    tag, *args = tree
    if tag == 'leaf':
        return LITERALS[args[0]]
    if tag == 'shift':
        return evaluate(args[0]) << args[1]
    return evaluate(args[0]) + evaluate(args[1])


def leaf_offsets(tree, offset=0):
    tag, *args = tree
    if tag == 'leaf':
        return [(args[0], offset)]
    if tag == 'shift':
        return leaf_offsets(args[0], offset + args[1])
    return leaf_offsets(args[0], offset) + leaf_offsets(args[1], offset)


def lanes(value, width, count):
    if width % 4 == 0:
        digits = width // 4
        encoded = f'{value:0{digits * count}x}'
        assert len(encoded) == digits * count
        return array('I', (int(encoded[i:i+digits], 16)
                           for i in range(len(encoded)-digits, -1, -digits)))
    return array('I', ((value >> (width*i)) % (2**width) for i in range(count)))


TREES = {name: expression(name)
         for name in ('rawClass', 'representatives', 'destinations', 'edgeKinds')}
PACKED = {name: evaluate(tree) for name, tree in TREES.items()}
OFFSETS = dict(leaf_offsets(TREES['rawClass']))
raw = lanes(PACKED['rawClass'], 12, 4**10)
representatives = lanes(PACKED['representatives'], 20, 3741)
destinations = lanes(PACKED['destinations'], 12, 4*3741)
kinds = lanes(PACKED['edgeKinds'], 2, 4*3741)
assert len(OFFSETS) == 768
ordered_offsets = sorted((offset, name) for name, offset in OFFSETS.items())
for j, (offset, name) in enumerate(ordered_offsets):
    upper = ordered_offsets[j+1][0] if j+1 < len(ordered_offsets) else 12*4**10
    assert LITERALS[name] < 2**(upper-offset), (name, 'overlap')

STEPS = ((1, 0), (0, 1), (-1, 0), (0, -1))
COUNTS = [1] + [0]*10
WINDOWS = {}
used = set()
vertices = [(0, 0)]


def bond(x, y):
    return (x, y) if x < y else (y, x)


def generate(code, word):
    n = len(word)
    if n == 10:
        WINDOWS[code] = (tuple(word), tuple(vertices), frozenset(used))
        return
    x = vertices[-1]
    for d, step in enumerate(STEPS):
        y = (x[0]+step[0], x[1]+step[1])
        edge = bond(x, y)
        if edge in used:
            continue
        COUNTS[n+1] += 1
        used.add(edge)
        vertices.append(y)
        generate(4*code+d, word+(d,))
        vertices.pop()
        used.remove(edge)


generate(0, ())
assert COUNTS == [1, 4, 12, 36, 108, 316, 916, 2628, 7500, 21268, 60092]
valid_codes = set(WINDOWS)
coverage_errors = [code for code, a in enumerate(raw)
                   if a > 3741 or ((a < 3741) != (code in valid_codes))]
assert not coverage_errors, coverage_errors[:10]
assert set(raw[c] for c in WINDOWS) == set(range(3741))
for a, code in enumerate(representatives):
    assert code < 4**10 and code in WINDOWS and raw[code] == a, (a, code)
for j, (dest, kind) in enumerate(zip(destinations, kinds)):
    assert dest <= 3741 and ((dest == 0) == (kind == 3)), (j, dest, kind)


def raw_transition(code, d):
    word, path, edges = WINDOWS[code]
    endpoint = path[-1]
    step = STEPS[d]
    target = (endpoint[0]+step[0], endpoint[1]+step[1])
    allowed = d != (word[-1]+2) % 4 and bond(endpoint, target) not in edges
    kind = 2 if endpoint in path[:-1] else (0 if d == word[-1] else 1)
    successor = 4*(code % (4**9)) + d
    return allowed, kind, successor, word[-1]


errors = []
class_signatures = {}
for code in WINDOWS:
    a = raw[code]
    signature = []
    for d in range(4):
        allowed, kind, successor, arrival = raw_transition(code, d)
        rep_allowed, rep_kind, _, rep_arrival = raw_transition(representatives[a], d)
        signature.append((allowed, kind, raw[successor] if allowed else None))
        if allowed != (destinations[4*a+d] != 0):
            errors.append((code, d, 'stored admissibility'))
        if allowed != rep_allowed or kind != rep_kind:
            errors.append((code, d, 'representative admissibility/kind'))
        if allowed:
            if successor not in WINDOWS:
                errors.append((code, d, 'successor not raw'))
            if kinds[4*a+d] != kind:
                errors.append((code, d, 'stored kind'))
            if destinations[4*a+d]-1 != raw[successor]:
                errors.append((code, d, 'stored successor'))
            if kind != 2 and rep_arrival != arrival:
                errors.append((code, d, 'arrival'))
    signature = tuple(signature)
    if a in class_signatures and class_signatures[a] != signature:
        errors.append((code, 'class incompatibility'))
    class_signatures[a] = signature
assert not errors, errors[:10]
edge_counts = Counter(k for dest, k in zip(destinations, kinds) if dest)
assert edge_counts == {0: 2516, 1: 5032, 2: 1872}, edge_counts

summary = {
    'source': str(SOURCE),
    'depth_counts': COUNTS,
    'raw_lanes': len(raw),
    'coverage_errors': len(coverage_errors),
    'classes': len(class_signatures),
    'representatives_checked': len(representatives),
    'stored_class_direction_slots_checked': len(destinations),
    'raw_direction_comparisons': 4*len(WINDOWS),
    'transition_errors': len(errors),
    'edge_counts': dict(edge_counts),
    'assigned': {},
}
for i in range(465, 470):
    name = f'rawClass_{i}'
    offset = OFFSETS[name]
    width = 16384
    first = offset // 12
    last = (offset+width-1) // 12
    valid = [code for code in range(first, last+1) if code in WINDOWS]
    classes = {raw[c] for c in valid}
    successor_uses = sum(raw_transition(c,d)[0] and first <= raw_transition(c,d)[2] <= last
                         for c in WINDOWS for d in range(4))
    summary['assigned'][name] = {
        'line': TEXT[:TEXT.index('private noncomputable def '+name+' ')].count('\n')+1,
        'bit_offset': offset,
        'bit_end_exclusive': offset+width,
        'lane_first': first,
        'lane_last': last,
        'lanes_touched': last-first+1,
        'valid_lanes_touched': len(valid),
        'invalid_lanes_touched': last-first+1-len(valid),
        'distinct_classes_touched': len(classes),
        'admissible_successors_into_lane_range': successor_uses,
        'coverage_errors': 0,
        'transition_errors': 0,
    }

print(json.dumps(summary, indent=2))
