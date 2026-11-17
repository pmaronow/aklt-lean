"""Read-only reconstruction of the paper's memory-ten data contract."""

import ast
from collections import Counter
from pathlib import Path
import re


SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
text = SOURCE.read_text()
literals = {}
literal_lines = {}
for lineno, line in enumerate(text.splitlines(), 1):
    match = re.fullmatch(r'private noncomputable def (\w+) : ℕ := 0x([0-9a-f]+)', line)
    if match:
        name, digits = match.groups()
        literals[name] = int(digits, 16)
        literal_lines[name] = lineno


def evaluate(node):
    """Evaluate the explicitly parenthesized Nat additions and shifts."""
    if isinstance(node, ast.Name):
        return literals[node.id], {node.id: 0}
    if isinstance(node, ast.Constant):
        return node.value, {}
    assert isinstance(node, ast.BinOp), ast.dump(node)
    left, left_offsets = evaluate(node.left)
    right, right_offsets = evaluate(node.right)
    if isinstance(node.op, ast.LShift):
        assert not right_offsets
        return left << right, {name: offset + right for name, offset in left_offsets.items()}
    assert isinstance(node.op, ast.Add)
    assert not (left & right), 'Nonzero overlap in packed addition'
    assert left_offsets.keys().isdisjoint(right_offsets)
    return left + right, left_offsets | right_offsets


tables = {}
offsets = {}
for name in ('rawClass', 'representatives', 'destinations', 'edgeKinds'):
    expression = re.search(rf'^noncomputable def {name} : ℕ := (.+)$', text, re.M).group(1)
    value, leaves = evaluate(ast.parse(expression.replace('<<<', '<<'), mode='eval').body)
    tables[name] = value
    offsets[name] = leaves
    print(f'{name}: {len(leaves)} literal chunks; {value.bit_length()} significant bits')
assert set(literals) == set().union(*(set(leaves) for leaves in offsets.values()))


def lanes(name, width, count):
    # Read little-endian bytes so no large-integer shift is repeated per lane.
    data = tables[name].to_bytes((width * count + 7) // 8, 'little')
    result = []
    for i in range(count):
        bit = i * width
        start, rem = divmod(bit, 8)
        size = (rem + width + 7) // 8
        result.append((int.from_bytes(data[start:start + size], 'little') >> rem) & ((1 << width) - 1))
    return result


classes = lanes('rawClass', 12, 4**10)
representatives = lanes('representatives', 20, 3741)
destinations = lanes('destinations', 12, 3741 * 4)
kinds = lanes('edgeKinds', 2, 3741 * 4)
assert max(classes) <= 3741
assert max(representatives) < 4**10
assert max(destinations) <= 3741
assert all((dest == 0) == (kind == 3) for dest, kind in zip(destinations, kinds))

STEPS = ((1, 0), (0, 1), (-1, 0), (0, -1))
counts = [0] * 11
raw = {}


def bond(x, y):
    return tuple(sorted((x, y)))


def generate(word=(), vertices=((0, 0),), used=frozenset(), code=0):
    counts[len(word)] += 1
    if len(word) == 10:
        raw[code] = (word, vertices, used)
        return
    x, y = vertices[-1]
    for d, (dx, dy) in enumerate(STEPS):
        nxt = (x + dx, y + dy)
        edge = bond(vertices[-1], nxt)
        if edge not in used:
            generate(word + (d,), vertices + (nxt,), used | {edge}, code * 4 + d)


generate()
print('Regenerated raw counts:', counts)
assert counts[1:] == [4, 12, 36, 108, 316, 916, 2628, 7500, 21268, 60092]
assert list(raw) == sorted(raw)
assert {i for i, a in enumerate(classes) if a < 3741} == raw.keys()
assert {classes[code] for code in raw} == set(range(3741))
for a, code in enumerate(representatives):
    assert code in raw and classes[code] == a
print('Coverage, range, representative validity and surjectivity: PASS')


def raw_row(code):
    word, vertices, used = raw[code]
    endpoint = vertices[-1]
    revisit = endpoint in vertices[:-1]
    rows = []
    for d, (dx, dy) in enumerate(STEPS):
        nxt = (endpoint[0] + dx, endpoint[1] + dy)
        allowed = d != (word[-1] + 2) % 4 and bond(endpoint, nxt) not in used
        kind = 2 if revisit else (0 if d == word[-1] else 1)
        successor = (code % 4**9) * 4 + d
        rows.append((allowed, kind, successor))
    return rows


admitted = 0
for code, (word, _, _) in raw.items():
    a = classes[code]
    rep = representatives[a]
    rep_rows = raw_row(rep)
    for d, (allowed, kind, successor) in enumerate(raw_row(code)):
        idx = 4 * a + d
        assert allowed == (destinations[idx] != 0), ('allowed', code, a, d)
        assert allowed == rep_rows[d][0], ('representative allowed', code, a, d)
        assert kind == rep_rows[d][1], ('representative kind', code, a, d)
        if allowed:
            admitted += 1
            assert kinds[idx] == kind == rep_rows[d][1], ('kind', code, a, d)
            assert successor in raw, ('successor raw', code, a, d)
            assert destinations[idx] - 1 == classes[successor], ('successor', code, a, d)
            if kind != 2:
                assert word[-1] == raw[rep][0][-1], ('arrival', code, a, d)
edge_counts = Counter(kind for dest, kind in zip(destinations, kinds) if dest)
assert edge_counts == {0: 2516, 1: 5032, 2: 1872}
print(f'All raw rows and {admitted} admitted raw transitions: PASS')
print('Quotient edge counts (0=straight, 1=turn, 2=revisit):', dict(sorted(edge_counts.items())))

for n in range(320, 325):
    name = f'rawClass_{n}'
    low = offsets['rawClass'][name]
    high = low + 16384 - 1
    first, last = low // 12, high // 12
    entries = range(first, last + 1)
    valid = [code for code in entries if code in raw]
    affected_transitions = sum(sum(row[0] for row in raw_row(code)) for code in valid)
    print(f'{name} line {literal_lines[name]}: bit interval [{low},{high}], '
          f'code interval [{first},{last}], boundary offsets {low % 12},{high % 12}; '
          f'{len(valid)} raw, {len(entries) - len(valid)} invalid, '
          f'{affected_transitions} admitted transitions; PASS')
