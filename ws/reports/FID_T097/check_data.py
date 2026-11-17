"""Read-only reconstruction of the automaton's finite paper contract."""
import ast
from collections import Counter
import hashlib
import json
from pathlib import Path
import re

SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
source = SOURCE.read_text()
literals = {
    m[1]: int(m[2], 16)
    for m in re.finditer(r'^private noncomputable def (\w+) : ℕ := 0x([0-9a-f]+)$', source, re.M)
}


def unpack_expression(name):
    expr = re.search(r'^noncomputable def ' + name + r' : ℕ := (.+)$', source, re.M)[1]
    tree = ast.parse(expr.replace('<<<', '<<'), mode='eval').body
    offsets = {}

    def visit(node, offset=0):
        if isinstance(node, ast.Name):
            assert node.id not in offsets
            offsets[node.id] = offset
            return literals[node.id] << offset
        assert isinstance(node, ast.BinOp)
        if isinstance(node.op, ast.Add):
            return visit(node.left, offset) + visit(node.right, offset)
        assert isinstance(node.op, ast.LShift) and isinstance(node.right, ast.Constant)
        return visit(node.left, offset + node.right.value)

    packed = visit(tree)
    ordered = sorted(offsets.items(), key=lambda pair: pair[1])
    for (low, low_offset), (_, high_offset) in zip(ordered, ordered[1:]):
        assert literals[low].bit_length() <= high_offset - low_offset
    return packed, offsets


raw_packed, offsets = unpack_expression('rawClass')
raw_hex = format(raw_packed, 'x').zfill(3 * 4**10)
assert len(raw_hex) == 3 * 4**10
raw = [int(raw_hex[i:i+3], 16) for i in range(0, len(raw_hex), 3)][::-1]


def lanes(name, width, count):
    packed, _ = unpack_expression(name)
    mask = (1 << width) - 1
    result = []
    for _ in range(count):
        result.append(packed & mask)
        packed >>= width
    assert packed == 0
    return result


representatives = lanes('representatives', 20, 3741)
destinations = lanes('destinations', 12, 4 * 3741)
kinds = lanes('edgeKinds', 2, 4 * 3741)
steps = ((1, 0), (0, 1), (-1, 0), (0, -1))


def add(p, d):
    dx, dy = steps[d]
    return p[0] + dx, p[1] + dy


def bond(p, q):
    return tuple(sorted((p, q)))


depth_counts = [0] * 11
models = {}


def generate(word=(), positions=((0, 0),), used=frozenset(), code=0):
    depth_counts[len(word)] += 1
    if len(word) == 10:
        endpoint = positions[-1]
        revisit = endpoint in positions[:-1]
        admissible = []
        raw_kinds = []
        for d in range(4):
            admissible.append(d != (word[-1] + 2) % 4 and bond(endpoint, add(endpoint, d)) not in used)
            raw_kinds.append(2 if revisit else 0 if d == word[-1] else 1)
        models[code] = (word[-1], tuple(admissible), tuple(raw_kinds))
        return
    p = positions[-1]
    for d in range(4):
        q = add(p, d)
        edge = bond(p, q)
        if edge not in used:
            generate(word + (d,), positions + (q,), used | {edge}, 4 * code + d)


generate()
errors = []


def check(ok, category, **details):
    if not ok:
        errors.append({'category': category, **details})


check(depth_counts[1:] == [4, 12, 36, 108, 316, 916, 2628, 7500, 21268, 60092], 'counts')
check(max(raw) <= 3741, 'raw bounds', maximum=max(raw))
listed_raw = {code for code, a in enumerate(raw) if a < 3741}
check(listed_raw == models.keys(), 'raw coverage', missing=sorted(models.keys() - listed_raw)[:20], extra=sorted(listed_raw - models.keys())[:20])
for a, code in enumerate(representatives):
    check(code < 4**10 and code in models, 'representative validity', a=a, code=code)
    check(raw[code] == a, 'representative image', a=a, code=code, image=raw[code])

for code, (arrival, admissible, raw_kinds) in models.items():
    a = raw[code]
    if a >= 3741:
        continue
    rep = models.get(representatives[a])
    if rep is None:
        continue
    check(admissible == rep[1], 'representative admissibility', code=code, a=a)
    check(raw_kinds == rep[2], 'representative kinds including inadmissible directions', code=code, a=a)
    for d in range(4):
        dest = destinations[4 * a + d]
        kind = kinds[4 * a + d]
        check(dest <= 3741, 'destination bounds', a=a, d=d, dest=dest)
        check((dest == 0) == (kind == 3), 'forbidden edge encoding', a=a, d=d)
        check(bool(dest) == admissible[d], 'stored admissibility', code=code, a=a, d=d)
        if admissible[d]:
            check(kind == raw_kinds[d], 'stored kind', code=code, a=a, d=d, actual=kind, expected=raw_kinds[d])
            successor = (code % 4**9) * 4 + d
            check(successor in models, 'successor validity', code=code, d=d)
            check(dest - 1 == raw[successor], 'successor image', code=code, a=a, d=d, actual=dest - 1, expected=raw[successor])
            if raw_kinds[d] != 2:
                check(arrival == rep[0], 'nonrevisit arrival', code=code, a=a, d=d)

edge_counts = Counter(kinds[i] for i, dest in enumerate(destinations) if dest != 0)
check(edge_counts == {0: 2516, 1: 5032, 2: 1872}, 'edge counts', actual=dict(edge_counts))

# Also reconstruct the text format described in the paper. The docstring's
# digest is corroborating metadata; the finite checks above are independent.
rows = ['60092 3741']
rows += [f'{code} {raw[code]}' for code in sorted(models)]
for a, code in enumerate(representatives):
    row = [code] + [destinations[4*a+d] - 1 for d in range(4)] + [kinds[4*a+d] if kinds[4*a+d] != 3 else -1 for d in range(4)]
    rows.append(' '.join(map(str, row)))
archive_text = '\n'.join(rows) + '\n'
archive_hash = hashlib.sha256(archive_text.encode()).hexdigest()
docstring_hash = re.search(r'Archive SHA-256: ([0-9a-f]+)', source)[1]

blocks = []
for i in range(450, 455):
    name = f'rawClass_{i}'
    offset = offsets[name]
    first, last = offset // 12, (offset + 16383) // 12
    affected = range(first, last + 1)
    valid = [code for code in affected if code in models]
    block_errors = [e for e in errors if e.get('code') in affected]
    blocks.append({
        'name': name, 'line': 15 + 2*i,
        'bit_interval_half_open': [offset, offset + 16384],
        'raw_code_interval_inclusive': [first, last],
        'raw_windows': len(valid), 'invalid_words': last - first + 1 - len(valid),
        'first_valid_example': None if not valid else {'code': valid[0], 'word': ''.join('ENWS'[(valid[0] // 4**j) % 4] for j in reversed(range(10))), 'class': raw[valid[0]]},
        'errors_for_affected_codes': len(block_errors),
        'literal_sha256': hashlib.sha256(literals[name].to_bytes(2048, 'big')).hexdigest(),
    })

result = {
    'source_sha256': hashlib.sha256(source.encode()).hexdigest(),
    'raw_chunk_offsets_correct': all(offsets[f'rawClass_{i}'] == (767-i)*16384-4 for i in range(767)) and offsets['rawClass_767'] == 0,
    'depth_counts': depth_counts, 'raw_table_length': len(raw),
    'raw_table_range': [min(raw), max(raw)], 'listed_raw_count': len(listed_raw),
    'representative_count': len(representatives), 'labelled_edge_counts': dict(edge_counts),
    'reconstructed_text_sha256': archive_hash, 'docstring_archive_sha256': docstring_hash,
    'reconstructed_text_matches_docstring_sha256': archive_hash == docstring_hash,
    'error_count': len(errors), 'first_errors': errors[:20], 'blocks': blocks,
}
print(json.dumps(result, indent=2))
Path('check_results.json').write_text(json.dumps(result, indent=2) + '\n')
