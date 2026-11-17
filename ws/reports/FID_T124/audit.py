"""Independent finite checks using only the supplied Lean literals and trail rules."""
import ast
from collections import Counter
import json
from pathlib import Path
import re

SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
text = SOURCE.read_text()
values = {}
nodes = {}
lines = {}
for lineno, line in enumerate(text.splitlines(), 1):
    m = re.fullmatch(r'(?:private )?noncomputable def (\w+) : ℕ := (.*)', line)
    if m:
        name, body = m.groups()
        nodes[name] = ast.parse(body.replace('<<<', '<<'), mode='eval').body
        lines[name] = lineno


def evaluate(node):
    if isinstance(node, ast.Constant) and isinstance(node.value, int):
        return node.value
    if isinstance(node, ast.Name):
        return values[node.id]
    if isinstance(node, ast.BinOp):
        a, b = evaluate(node.left), evaluate(node.right)
        if isinstance(node.op, ast.Add):
            assert a & b == 0, 'overlapping nonzero bits in packed addition'
            return a + b
        if isinstance(node.op, ast.LShift):
            return a << b
    raise ValueError(ast.dump(node))


for name, node in nodes.items():
    values[name] = evaluate(node)


def leaves(node, offset=0):
    if isinstance(node, ast.Name):
        return [(node.id, offset)]
    assert isinstance(node, ast.BinOp)
    if isinstance(node.op, ast.Add):
        return leaves(node.left, offset) + leaves(node.right, offset)
    assert isinstance(node.op, ast.LShift)
    return leaves(node.left, offset + evaluate(node.right))


def lanes(name, width, count):
    # Decode little-endian lanes without repeatedly shifting a multi-megabit int.
    v = values[name]
    raw = v.to_bytes((width * count + 7) // 8, 'little')
    mask = (1 << width) - 1
    return [
        (int.from_bytes(raw[(width*i)//8:(width*i+width+7)//8], 'little')
         >> ((width*i) % 8)) & mask
        for i in range(count)
    ]


raw_classes = lanes('rawClass', 12, 4**10)
reps = lanes('representatives', 20, 3741)
dest = lanes('destinations', 12, 3741*4)
kinds = lanes('edgeKinds', 2, 3741*4)
offsets = dict(leaves(nodes['rawClass']))

print('packed bits:', {n: values[n].bit_length() for n in
                        ['rawClass', 'representatives', 'destinations', 'edgeKinds']})
print('raw class range/histogram top:', min(raw_classes), max(raw_classes),
      Counter(raw_classes).most_common(5))
print('assigned chunk offsets and intersecting codes:')
for k in range(585, 590):
    name = f'rawClass_{k}'
    offset = offsets[name]
    low, high = offset // 12, (offset + 16384 - 1) // 12
    print(name, 'line', lines[name], 'offset', offset,
          'phase', offset % 12, 'codes', low, high,
          'raw range', min(raw_classes[low:high+1]), max(raw_classes[low:high+1]),
          'valid-coded', sum(a < 3741 for a in raw_classes[low:high+1]))

STEPS = [(1, 0), (0, 1), (-1, 0), (0, -1)]


def decode(code, n=10):
    return [(code >> (2*(n-1-i))) & 3 for i in range(n)]


def bond(x, y):
    return tuple(sorted((x, y)))


def geometry(word):
    vertices = [(0, 0)]
    bonds = set()
    valid = True
    for d in word:
        x, y = vertices[-1]
        dx, dy = STEPS[d]
        endpoint = (x+dx, y+dy)
        edge = bond((x, y), endpoint)
        if edge in bonds:
            valid = False
        bonds.add(edge)
        vertices.append(endpoint)
    return valid, vertices, bonds


def edge_data(word):
    valid, vertices, bonds = geometry(word)
    assert valid
    x, y = vertices[-1]
    revisit = vertices[-1] in vertices[:-1]
    output = []
    for d, (dx, dy) in enumerate(STEPS):
        allowed = d != (word[-1]+2) % 4 and bond((x, y), (x+dx, y+dy)) not in bonds
        kind = 2 if revisit else (0 if d == word[-1] else 1)
        output.append((allowed, kind))
    return output


if __name__ == '__main__':
    errors = Counter()
    examples = {}

    def record(key, value):
        errors[key] += 1
        examples.setdefault(key, value)

    # Independently enumerate all raw words by unused undirected bonds.
    valid_codes = set()
    depth_counts = Counter()

    def extend(vertices, bonds, code, depth):
        depth_counts[depth] += 1
        if depth == 10:
            valid_codes.add(code)
            return
        x, y = vertices[-1]
        for d, (dx, dy) in enumerate(STEPS):
            end = (x+dx, y+dy)
            edge = bond((x, y), end)
            if edge not in bonds:
                extend(vertices+[end], bonds | {edge}, code*4+d, depth+1)

    extend([(0, 0)], set(), 0, 0)
    print('independent counts by length:', dict(sorted(depth_counts.items())))
    for code, a in enumerate(raw_classes):
        if a > 3741 or (a < 3741) != (code in valid_codes):
            record('coverage', (code, a, code in valid_codes))
    for a, code in enumerate(reps):
        if code not in valid_codes or raw_classes[code] != a:
            record('representative', (a, code, raw_classes[code]))

    rep_edges = [edge_data(decode(c)) if c in valid_codes else None for c in reps]
    for a, edges in enumerate(rep_edges):
        if edges is None:
            continue
        for d, (allowed, kind) in enumerate(edges):
            idx = a*4+d
            if (dest[idx] != 0) != allowed:
                record('stored_admissibility', (a, d, dest[idx], allowed))
            if kinds[idx] != (kind if allowed else 3):
                record('stored_kind', (a, d, kinds[idx], kind, allowed))
            if not (0 <= dest[idx] <= 3741):
                record('stored_destination_range', (a, d, dest[idx]))

    class_members = Counter()
    for code in sorted(valid_codes):
        a = raw_classes[code]
        if a >= 3741:
            continue
        class_members[a] += 1
        word = decode(code)
        edges = edge_data(word)
        for d, (allowed, kind) in enumerate(edges):
            idx = a*4+d
            if (dest[idx] != 0) != allowed:
                record('raw_admissibility', (code, a, d, allowed, dest[idx]))
            if kind != rep_edges[a][d][1]:
                record('all_direction_kind_vs_rep', (code, a, d, kind, rep_edges[a][d][1]))
            if allowed:
                if kinds[idx] != kind:
                    record('raw_kind', (code, a, d, kind, kinds[idx]))
                successor = (code % (4**9))*4+d
                if dest[idx]-1 != raw_classes[successor]:
                    record('raw_successor', (code, a, d, successor, dest[idx]-1, raw_classes[successor]))
                if kind != 2 and word[-1] != reps[a] % 4:
                    record('raw_nonrevisit_arrival', (code, a, d, word[-1], reps[a] % 4))

    print('distinct represented classes:', len(class_members))
    print('labelled edge counts:', dict(Counter(k for dst, k in zip(dest, kinds) if dst)))
    print('errors:', dict(errors))
    print('first examples:', examples)
    result = {
        'depth_counts': dict(sorted(depth_counts.items())),
        'errors': dict(errors),
        'examples': examples,
        'assigned': [],
    }
    for k in range(585, 590):
        name = f'rawClass_{k}'
        lo = offsets[name] // 12
        hi = (offsets[name] + 16384 - 1) // 12
        valid = [c for c in range(lo, hi+1) if c in valid_codes]
        item = dict(name=name, source_line=lines[name], offset=offsets[name],
                    low_code=lo, high_code=hi, intersecting_lanes=hi-lo+1,
                    valid=len(valid), invalid=hi-lo+1-len(valid),
                    class_count=len({raw_classes[c] for c in valid}),
                    first_valid=(valid[0], raw_classes[valid[0]]) if valid else None,
                    last_valid=(valid[-1], raw_classes[valid[-1]]) if valid else None)
        result['assigned'].append(item)
        print('assigned summary:', item)
    Path('audit-results.json').write_text(json.dumps(result, indent=2)+'\n')
