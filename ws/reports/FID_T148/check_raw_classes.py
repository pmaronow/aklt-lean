"""Read-only audit of the literal memory-ten quotient against the paper model."""
from pathlib import Path
from collections import Counter
import ast
import hashlib
import json
import re

SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
TEXT = SOURCE.read_text()
VALUES = {}
EXPRESSIONS = {}
LINES = {}


def evaluate(node):
    if isinstance(node, ast.Constant):
        return node.value
    if isinstance(node, ast.Name):
        return VALUES[node.id]
    assert isinstance(node, ast.BinOp)
    a, b = evaluate(node.left), evaluate(node.right)
    if isinstance(node.op, ast.Add):
        return a + b
    assert isinstance(node.op, ast.LShift)
    return a << b


for line_no, line in enumerate(TEXT.splitlines(), 1):
    m = re.fullmatch(r'(?:private )?noncomputable def (\w+) : ℕ := (.+)', line)
    if m:
        name, expression = m.groups()
        node = ast.parse(expression.replace('<<<', '<<'), mode='eval').body
        VALUES[name] = evaluate(node)
        EXPRESSIONS[name] = node
        LINES[name] = line_no


def offsets(node, base=0):
    if isinstance(node, ast.Name):
        return [(node.id, base)]
    assert isinstance(node, ast.BinOp)
    if isinstance(node.op, ast.Add):
        return offsets(node.left, base) + offsets(node.right, base)
    assert isinstance(node.op, ast.LShift)
    return offsets(node.left, base + evaluate(node.right))


RAW_OFFSETS = dict(offsets(EXPRESSIONS['rawClass']))
assert len(RAW_OFFSETS) == 768
for i in range(768):
    name = f'rawClass_{i}'
    width = 16380 if i == 767 else 16384
    assert VALUES[name] < (1 << width)
    expected_offset = (767-i)*16384-4 if i < 767 else 0
    assert RAW_OFFSETS[name] == expected_offset


def lanes(name, width, count):
    value = VALUES[name]
    assert value < 1 << (width * count)
    data = value.to_bytes((width*count+7)//8, 'little')
    result = []
    for i in range(count):
        bit = width*i
        first = bit//8
        stop = (bit+width+7)//8
        result.append((int.from_bytes(data[first:stop], 'little') >> (bit % 8)) & ((1 << width)-1))
    return result


classes = lanes('rawClass', 12, 4**10)
reps = lanes('representatives', 20, 3741)
dest = lanes('destinations', 12, 3741*4)
kinds = lanes('edgeKinds', 2, 3741*4)
STEPS = ((1, 0), (0, 1), (-1, 0), (0, -1))


def model(word):
    x = (0, 0)
    vertices = [x]
    bonds = set()
    valid = True
    for d in word:
        dx, dy = STEPS[d]
        y = (x[0]+dx, x[1]+dy)
        bond = frozenset((x, y))
        if bond in bonds:
            valid = False
        bonds.add(bond)
        vertices.append(y)
        x = y
    allowed = []
    for d, (dx, dy) in enumerate(STEPS):
        new_bond = frozenset((x, (x[0]+dx, x[1]+dy)))
        allowed.append(d != (word[-1]+2) % 4 and new_bond not in bonds)
    revisit = x in vertices[:-1]
    kind = [2 if revisit else 0 if d == word[-1] else 1 for d in range(4)]
    return valid, allowed, kind, word[-1]


def decode(code):
    return tuple((code >> (2*(9-i))) & 3 for i in range(10))


generated = {}
depth_counts = [1] + [0]*10


def generate(word=(), x=(0, 0), bonds=frozenset(), code=0):
    if len(word) == 10:
        generated[code] = word
        return
    for d, (dx, dy) in enumerate(STEPS):
        y = (x[0]+dx, x[1]+dy)
        bond = frozenset((x, y))
        if bond not in bonds:
            depth_counts[len(word)+1] += 1
            generate(word+(d,), y, bonds | {bond}, code*4+d)


generate()
errors = []
coverage_errors = []
for code, cls in enumerate(classes):
    if cls > 3741 or ((cls < 3741) != (code in generated)):
        coverage_errors.append((code, cls, code in generated))
errors.extend(('coverage', *e) for e in coverage_errors)

for a, code in enumerate(reps):
    if code not in generated or classes[code] != a:
        errors.append(('representative', a, code, classes[code]))

edge_counts = Counter()
for a, code in enumerate(reps):
    valid, allowed, kind, arrival = model(decode(code))
    for d in range(4):
        j = a*4+d
        if dest[j] > 3741 or ((dest[j] == 0) != (kinds[j] == 3)):
            errors.append(('row-range', a, d, dest[j], kinds[j]))
        if (dest[j] != 0) != allowed[d]:
            errors.append(('representative-admissibility', a, d))
        if allowed[d]:
            if kinds[j] != kind[d]:
                errors.append(('representative-kind', a, d))
            edge_counts[kinds[j]] += 1

for code, word in generated.items():
    a = classes[code]
    if a >= 3741:
        continue
    valid, allowed, kind, arrival = model(word)
    rep_model = model(decode(reps[a]))
    if allowed != rep_model[1] or kind != rep_model[2]:
        errors.append(('class-admissibility-kind', code, a))
    for d in range(4):
        if allowed[d]:
            successor = ((code % (4**9))*4)+d
            if dest[a*4+d]-1 != classes[successor]:
                errors.append(('successor', code, a, d, dest[a*4+d]-1, classes[successor]))
            if kind[d] != 2 and arrival != reps[a] % 4:
                errors.append(('arrival', code, a, d))

selected = []
for i in range(705, 710):
    name = f'rawClass_{i}'
    start = RAW_OFFSETS[name]
    stop = start+16384
    first = start//12
    last = (stop-1)//12
    selected.append(dict(name=name, line=LINES[name], bit_start=start, bit_stop_exclusive=stop,
                         first_code=first, last_code=last,
                         raw_words=sum(c in generated for c in range(first, last+1)),
                         invalid_words=sum(c not in generated for c in range(first, last+1))))

archive_rows = [[60092, 3741]] + [[c, a] for c, a in enumerate(classes) if a < 3741]
for a in range(3741):
    archive_rows.append([reps[a]] + [d-1 for d in dest[a*4:a*4+4]] +
                        [-1 if k == 3 else k for k in kinds[a*4:a*4+4]])
archive_text = ''.join(' '.join(map(str, row))+'\n' for row in archive_rows)
archive_sha256 = hashlib.sha256(archive_text.encode()).hexdigest()
declared_sha256 = re.search(r'Archive SHA-256: ([0-9a-f]+)', TEXT)[1]
assert archive_sha256 == declared_sha256

result = dict(depth_counts=depth_counts, class_distribution=dict(Counter(classes).most_common(5)),
              distinct_valid_classes=len({classes[c] for c in generated}),
              edge_counts=dict(sorted(edge_counts.items())), total_errors=len(errors),
              first_errors=errors[:20], archive_sha256=archive_sha256,
              archive_hash_matches_declared_source=True, selected=selected)
Path('check_results.json').write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps(result, indent=2))
assert not errors
