"""Independent finite review of the supplied Lean automaton data.
Reads only the assigned Lean input. No Lean process or external witness is used.
"""
from pathlib import Path
from collections import Counter
import re
import json

SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
s = SOURCE.read_text()
literals = {}
line_numbers = {}
for line_number, line in enumerate(s.splitlines(), 1):
    m = re.fullmatch(r'private noncomputable def (\w+) : ℕ := (0x[0-9a-fA-F]+)', line)
    if m:
        literals[m[1]] = (int(m[2], 16), 4 * len(m[2][2:]))
        line_numbers[m[1]] = line_number
assert len(literals) == 786

# Parse the actual composite expressions, retaining each literal's bit offset.
def composite(name):
    expression = re.search(rf'^noncomputable def {name} : ℕ := (.*)$', s, re.M)[1]
    tokens = re.findall(r'<<<|\w+|[()+]', expression)
    assert ''.join(tokens) == re.sub(r'\s+', '', expression)
    cursor = 0
    def atom():
        nonlocal cursor
        t = tokens[cursor]
        cursor += 1
        if t == '(':
            result = expr()
            assert tokens[cursor] == ')'
            cursor += 1
            return result
        if t.isdecimal():
            return int(t), {}
        value, width = literals[t]
        return value, {t: 0}
    def expr():
        nonlocal cursor
        result, offsets = atom()
        while cursor < len(tokens) and tokens[cursor] != ')':
            op = tokens[cursor]
            cursor += 1
            rhs, more = atom()
            if op == '<<<':
                assert not more
                result <<= rhs
                offsets = {k: v + rhs for k, v in offsets.items()}
            else:
                assert op == '+' and not offsets.keys() & more.keys()
                result += rhs
                offsets.update(more)
        return result, offsets
    result, offsets = expr()
    assert cursor == len(tokens)
    intervals = sorted((v, v + literals[k][1], k) for k, v in offsets.items())
    assert intervals[0][0] == 0
    assert all(a[1] == b[0] for a, b in zip(intervals, intervals[1:]))
    assert result == sum(literals[k][0] << v for k, v in offsets.items())
    print(name, 'chunks', len(offsets), 'allocated bits', intervals[-1][1], 'actual bits', result.bit_length())
    return result, offsets

raw, offsets = composite('rawClass')
rep_packed, _ = composite('representatives')
dest_packed, _ = composite('destinations')
kind_packed, _ = composite('edgeKinds')

def lanes(packed, width, count):
    buf = packed.to_bytes(max((packed.bit_length()+7)//8, (width*count+7)//8), 'little')
    mask = (1 << width) - 1
    return [(int.from_bytes(buf[(i*width)//8:(i*width+width+7)//8], 'little') >> ((i*width)%8)) & mask for i in range(count)]

classes = lanes(raw, 12, 4**10)
representatives = lanes(rep_packed, 20, 3741)
destinations = lanes(dest_packed, 12, 3741*4)
kinds = lanes(kind_packed, 2, 3741*4)
assert max(classes) == 3741
assert max(representatives) < 4**10
assert max(destinations) <= 3741
assert all((d == 0) == (k == 3) for d, k in zip(destinations, kinds))
assert all(d == 0 or k < 3 for d, k in zip(destinations, kinds))

steps = [(1, 0), (0, 1), (-1, 0), (0, -1)]
windows = {}
counts = [0]*11

def edge(a, b):
    return tuple(sorted((a, b)))

def generate(word, code, vertices, bonds):
    depth = len(word)
    counts[depth] += 1
    if depth == 10:
        windows[code] = (tuple(word), tuple(vertices), frozenset(bonds))
        return
    x, y = vertices[-1]
    for d, (dx, dy) in enumerate(steps):
        nxt = (x+dx, y+dy)
        e = edge(vertices[-1], nxt)
        if e not in bonds:
            generate(word+[d], code*4+d, vertices+[nxt], bonds | {e})
generate([], 0, [(0, 0)], set())
print('generated counts', counts)
assert counts == [1, 4, 12, 36, 108, 316, 916, 2628, 7500, 21268, 60092]
assert all((a < 3741) == (code in windows) for code, a in enumerate(classes))
assert all(code in windows and classes[code] == a for a, code in enumerate(representatives))

# Regenerate precisely the admissibility/kind/successor/final-direction fields.
def row(code):
    word, vertices, bonds = windows[code]
    x, y = vertices[-1]
    revisit = vertices[-1] in vertices[:-1]
    result = []
    for d, (dx, dy) in enumerate(steps):
        allowed = d != (word[-1]+2)%4 and edge(vertices[-1], (x+dx,y+dy)) not in bonds
        kind = 2 if revisit else 0 if d == word[-1] else 1
        successor = (code % 4**9)*4+d
        result.append((allowed, kind, successor))
    return result

representative_rows = [row(code) for code in representatives]
checks = Counter()
for code, (word, vertices, bonds) in windows.items():
    a = classes[code]
    for d, (allowed, kind, successor) in enumerate(row(code)):
        j = 4*a+d
        assert allowed == (destinations[j] != 0), ('allowed', code, a, d)
        # Also check all kinds against representatives, including blocked directions.
        assert kind == representative_rows[a][d][1], ('kind vs representative', code, a, d)
        checks['raw direction comparisons'] += 1
        if allowed:
            assert kind == kinds[j], ('stored kind', code, a, d)
            assert successor in windows
            assert classes[successor] == destinations[j]-1, ('successor', code, a, d, successor)
            checks['admissible directions'] += 1
            if kind != 2:
                assert word[-1] == representatives[a] % 4, ('arrival', code, a, d)
                checks['nonrevisit directions'] += 1

edge_counts = Counter(k for d, k in zip(destinations, kinds) if d != 0)
assert edge_counts == {0:2516, 1:5032, 2:1872}
print('class lane distribution', dict(sorted(Counter(classes).items())) if False else {'valid':sum(a<3741 for a in classes), 'sentinel':classes.count(3741)})
print('edge counts', dict(edge_counts))
print('checks', dict(checks))

result = []
for k in range(685, 690):
    name = f'rawClass_{k}'
    value, width = literals[name]
    offset = offsets[name]
    first, last = offset//12, (offset+width-1)//12
    touched = list(range(first, last+1))
    full = [i for i in touched if offset <= 12*i and 12*(i+1) <= offset+width]
    valid = [i for i in touched if i in windows]
    boundary = {i:classes[i] for i in touched if i not in full}
    record = dict(name=name, source_line=line_numbers[name], width=width, bit_offset=offset,
                  bit_end=offset+width-1, first_code=first, last_code=last,
                  full_lanes=len(full), touched_lanes=len(touched),
                  valid_touched=len(valid), invalid_touched=len(touched)-len(valid),
                  boundary_lanes=boundary,
                  first_valid_code=valid[0] if valid else None,
                  first_valid_class=classes[valid[0]] if valid else None)
    result.append(record)
    print(json.dumps(record))
Path('audit_results.json').write_text(json.dumps({'counts':counts, 'checks':dict(checks), 'edge_counts':dict(edge_counts), 'targets':result}, indent=2)+'\n')
print('ALL CHECKS PASSED')
