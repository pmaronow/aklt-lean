"""Read-only reconstruction of the Lean literal automaton and paper checks."""
from pathlib import Path
from array import array
from collections import Counter
import ast
import json
import re

SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
text = SOURCE.read_text()
literals = {
    name: digits for name, digits in re.findall(
        r'^private noncomputable def (\w+) : ℕ := 0x([0-9a-f]+)$', text, re.M)
}
env = {name: int(digits, 16) for name, digits in literals.items()}
tables = {}
expressions = {}
for name in ('rawClass', 'representatives', 'destinations', 'edgeKinds'):
    expression = re.search(r'^noncomputable def ' + name + r' : ℕ := (.*)$', text, re.M)[1]
    expressions[name] = expression.replace('<<<', '<<')
    tables[name] = eval(expressions[name], {'__builtins__': {}}, env)
    chunks = [literals[f'{name}_{i}'] for i in range(sum(k.startswith(name + '_') for k in literals))]
    assert tables[name] == int(''.join(chunks), 16), name

def offsets(node, offset=0):
    if isinstance(node, ast.Name):
        return {node.id: offset}
    if isinstance(node.op, ast.LShift):
        return offsets(node.left, offset + node.right.value)
    assert isinstance(node.op, ast.Add)
    return offsets(node.left, offset) | offsets(node.right, offset)

raw_offsets = offsets(ast.parse(expressions['rawClass'], mode='eval').body)
raw_hex = format(tables['rawClass'], 'x').zfill(3 * 4**10)
classes = array('H', (int(raw_hex[i:i+3], 16) for i in range(len(raw_hex)-3, -1, -3)))
assert len(classes) == 4**10

def lane(name, width, index):
    return (tables[name] >> (width * index)) & ((1 << width) - 1)

reps = [lane('representatives', 20, a) for a in range(3741)]
destinations = [[lane('destinations', 12, a*4+d) for d in range(4)] for a in range(3741)]
kinds = [[lane('edgeKinds', 2, a*4+d) for d in range(4)] for a in range(3741)]
steps = ((1, 0), (0, 1), (-1, 0), (0, -1))

def word(code):
    return tuple((code >> (2*(9-i))) & 3 for i in range(10))

def geometry(code):
    vertices = [(0, 0)]
    bonds = set()
    valid = True
    for d in word(code):
        x, y = vertices[-1]
        dx, dy = steps[d]
        endpoint = (x+dx, y+dy)
        bond = frozenset((vertices[-1], endpoint))
        valid &= bond not in bonds
        bonds.add(bond)
        vertices.append(endpoint)
    return valid, vertices, bonds

rep_geometry = [geometry(code) for code in reps]
rep_kinds = []
for code, (_, vertices, _) in zip(reps, rep_geometry):
    revisit = vertices[-1] in vertices[:-1]
    rep_kinds.append([2 if revisit else (0 if d == code % 4 else 1) for d in range(4)])

errors = Counter()
examples = {}
def error(kind, value):
    errors[kind] += 1
    examples.setdefault(kind, value)

for a, (code, (valid, _, _)) in enumerate(zip(reps, rep_geometry)):
    if code >= 4**10 or not valid or classes[code] != a:
        error('representative', dict(a=a, code=code, valid=valid, actual=classes[code]))
    for d in range(4):
        dest, kind = destinations[a][d], kinds[a][d]
        if not (dest <= 3741 and ((dest == 0) == (kind == 3)) and (dest == 0 or kind < 3)):
            error('row_encoding', dict(a=a, d=d, dest=dest, kind=kind))

valid_codes = set()
depth_counts = [0]*11
target_stats = {}
for j in range(720, 725):
    name = f'rawClass_{j}'
    low = raw_offsets[name]
    high = low + 4*len(literals[name])
    target_stats[j] = dict(line=15+2*j, low_bit=low, high_bit_exclusive=high,
                           first_code=low//12, last_code=(high-1)//12)

local_errors = {j: Counter() for j in target_stats}
local_examples = {j: {} for j in target_stats}
def word_error(kind, code, **details):
    value = dict(code=code, word=word(code), **details)
    error(kind, value)
    for j, stats in target_stats.items():
        if stats['first_code'] <= code <= stats['last_code']:
            local_errors[j][kind] += 1
            local_examples[j].setdefault(kind, value)

def visit(code, vertices, bonds, length):
    depth_counts[length] += 1
    endpoint = vertices[-1]
    if length == 10:
        valid_codes.add(code)
        a = classes[code]
        if a >= 3741:
            word_error('valid_word_class', code, actual=a)
            return
        revisit = endpoint in vertices[:-1]
        for d, (dx, dy) in enumerate(steps):
            bond = frozenset((endpoint, (endpoint[0]+dx, endpoint[1]+dy)))
            allowed = (d != ((code % 4 + 2) % 4)) and bond not in bonds
            kind = 2 if revisit else (0 if d == code % 4 else 1)
            if kind != rep_kinds[a][d]:
                word_error('representative_kind', code, a=a, d=d, actual=kind, expected=rep_kinds[a][d])
            dest = destinations[a][d]
            if allowed != (dest != 0):
                word_error('admissibility', code, a=a, d=d, expected=allowed, stored=dest)
            if allowed:
                if kinds[a][d] != kind:
                    word_error('admitted_kind', code, a=a, d=d, expected=kind, stored=kinds[a][d])
                successor = (code % 4**9)*4+d
                if classes[successor] != dest-1:
                    word_error('successor', code, a=a, d=d, successor=successor,
                               expected=classes[successor], stored=dest-1)
                if kind != 2 and code % 4 != reps[a] % 4:
                    word_error('arrival', code, a=a, d=d, expected=code%4, stored=reps[a]%4)
        return
    for d, (dx, dy) in enumerate(steps):
        successor = (endpoint[0]+dx, endpoint[1]+dy)
        bond = frozenset((endpoint, successor))
        if bond in bonds:
            continue
        visit(code*4+d, vertices+[successor], bonds | {bond}, length+1)

visit(0, [(0,0)], set(), 0)
for code, a in enumerate(classes):
    valid = code in valid_codes
    if a > 3741 or ((a < 3741) != valid):
        word_error('coverage', code, valid=valid, actual=a)

for j, stats in target_stats.items():
    affected = range(stats['first_code'], stats['last_code']+1)
    stats['affected_lanes'] = len(affected)
    stats['valid_lanes'] = sum(code in valid_codes for code in affected)
    stats['invalid_lanes'] = stats['affected_lanes'] - stats['valid_lanes']
    stats['errors'] = dict(local_errors[j])
    stats['examples'] = local_examples[j]
    valids = [c for c in affected if c in valid_codes]
    stats['sample_valid'] = [(c, word(c), classes[c]) for c in valids[:3]]

edge_counts = Counter(kinds[a][d] for a in range(3741) for d in range(4) if destinations[a][d])
result = dict(depth_counts=depth_counts, raw_class_range=[min(classes), max(classes)],
              valid_words=len(valid_codes), represented_classes=len({classes[c] for c in valid_codes}),
              edge_counts=dict(edge_counts), errors=dict(errors), examples=examples, targets=target_stats)
print(json.dumps(result, indent=2))
