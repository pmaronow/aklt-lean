"""Read-only reconstruction checks for the five assigned packed-data chunks."""
from pathlib import Path
from collections import Counter
import json
import re

ROOT = Path('/home/ubuntu/aklt/review/FID_T/lean')
SOURCE = ROOT / 'AKLT/Defs/Automaton10Data.lean'
text = SOURCE.read_text()
literals = {name: int(value, 16) for name, value in re.findall(
    r'private noncomputable def (\w+) : ℕ := 0x([0-9a-f]+)', text)}


def parse(expr):
    tokens = re.findall(r'\w+|<<<|[()+]', expr)
    pos = 0

    def atom():
        nonlocal pos
        token = tokens[pos]
        pos += 1
        if token == '(':
            tree = expression()
            assert tokens[pos] == ')'
            pos += 1
            return tree
        return int(token) if token.isdigit() else token

    def expression():
        nonlocal pos
        tree = atom()
        while pos < len(tokens) and tokens[pos] != ')':
            op = tokens[pos]
            pos += 1
            assert op in ('+', '<<<')
            tree = (op, tree, atom())
        return tree

    tree = expression()
    assert pos == len(tokens)
    return tree


def evaluate(tree):
    if isinstance(tree, int):
        return tree
    if isinstance(tree, str):
        return literals[tree]
    op, left, right = tree
    a, b = evaluate(left), evaluate(right)
    return a + b if op == '+' else a << b


def offsets(tree, offset=0):
    if isinstance(tree, str):
        return {tree: offset}
    assert isinstance(tree, tuple)
    op, left, right = tree
    if op == '<<<':
        assert isinstance(right, int)
        return offsets(left, offset + right)
    a, b = offsets(left, offset), offsets(right, offset)
    assert not a.keys() & b.keys()
    return a | b


tables = {}
table_offsets = {}
for name in ('rawClass', 'representatives', 'destinations', 'edgeKinds'):
    expr = re.search(r'^noncomputable def ' + name + r' : ℕ := (.+)$', text, re.M)[1]
    tree = parse(expr)
    table_offsets[name] = offsets(tree)
    packed = evaluate(tree)
    tables[name] = packed.to_bytes((packed.bit_length() + 7) // 8, 'little')
    ordered = sorted(table_offsets[name].items(), key=lambda item: item[1])
    for (lower, lo), (upper, hi) in zip(ordered, ordered[1:]):
        assert lo + literals[lower].bit_length() <= hi, (lower, upper, 'overlap')


def lane(name, width, index):
    bit = width * index
    byte, shift = divmod(bit, 8)
    data = tables[name][byte:byte + (width + shift + 7) // 8]
    return (int.from_bytes(data, 'little') >> shift) & ((1 << width) - 1)


SIZE = 4 ** 10
classes = [lane('rawClass', 12, code) for code in range(SIZE)]
steps = ((1, 0), (0, 1), (-1, 0), (0, -1))


def bond(x, y):
    return tuple(sorted((x, y)))


def add(x, d):
    return x[0] + steps[d][0], x[1] + steps[d][1]


def decode(code):
    return tuple((code >> (2 * (9 - i))) & 3 for i in range(10))


def geometry(word):
    vertices = [(0, 0)]
    bonds = []
    for d in word:
        y = add(vertices[-1], d)
        bonds.append(bond(vertices[-1], y))
        vertices.append(y)
    return vertices, bonds


raw = {}
counts = Counter()


def generate(word, code, vertices, used):
    counts[len(word)] += 1
    if len(word) == 10:
        raw[code] = (word, vertices, used)
        return
    for d in range(4):
        y = add(vertices[-1], d)
        edge = bond(vertices[-1], y)
        if edge not in used:
            generate(word + (d,), 4 * code + d, vertices + (y,), used | {edge})


generate((), 0, ((0, 0),), frozenset())
coverage_errors = [code for code, a in enumerate(classes)
                   if a > 3741 or (a < 3741) != (code in raw)]
assert not coverage_errors, coverage_errors[:10]
assert len(raw) == 60092
representatives = [lane('representatives', 20, a) for a in range(3741)]
for a, code in enumerate(representatives):
    assert code < SIZE and code in raw and classes[code] == a, (a, code)


def row(code, word, vertices, used):
    result = []
    endpoint = vertices[-1]
    revisit = endpoint in vertices[:-1]
    for d in range(4):
        allowed = d != ((word[-1] + 2) % 4) and bond(endpoint, add(endpoint, d)) not in used
        kind = 2 if revisit else (0 if d == word[-1] else 1)
        successor = classes[((code % (4 ** 9)) * 4) + d] if allowed else None
        result.append((allowed, kind, successor))
    return result


rep_rows = [row(code, *raw[code]) for code in representatives]
edge_counts = Counter()
for a, rep_code in enumerate(representatives):
    for d, (allowed, kind, successor) in enumerate(rep_rows[a]):
        stored_dest = lane('destinations', 12, 4 * a + d)
        stored_kind = lane('edgeKinds', 2, 4 * a + d)
        assert stored_dest <= 3741
        assert (stored_dest == 0) == (stored_kind == 3)
        assert (stored_dest != 0) == allowed, (a, d, 'admissibility')
        if allowed:
            assert stored_kind == kind and stored_dest - 1 == successor, (a, d, 'row')
            edge_counts[kind] += 1

for code, (word, vertices, used) in raw.items():
    a = classes[code]
    for d, (allowed, kind, successor) in enumerate(row(code, word, vertices, used)):
        rep_allowed, rep_kind, rep_successor = rep_rows[a][d]
        assert allowed == rep_allowed, (code, d, 'admissibility')
        # Paper's compatible-projection condition includes kinds on all directions.
        assert kind == rep_kind, (code, d, 'kind')
        if allowed:
            assert successor == rep_successor, (code, d, 'successor')
            if kind != 2:
                assert word[-1] == raw[representatives[a]][0][-1], (code, d, 'arrival')

summary = {
    'raw_counts_by_depth': dict(sorted(counts.items())),
    'coverage_errors': len(coverage_errors),
    'representatives_checked': len(representatives),
    'raw_rows_checked': len(raw),
    'labelled_edge_counts_by_kind': dict(sorted(edge_counts.items())),
    'chunks': {},
}
for number in range(260, 265):
    name = f'rawClass_{number}'
    offset = table_offsets['rawClass'][name]
    # All chunks here occupy 16384 bits, including any leading zero bits.
    start, stop = offset // 12, (offset + 16384 - 1) // 12 + 1
    valid = [code for code in range(start, stop) if code in raw]
    summary['chunks'][name] = {
        'source_line': 15 + 2 * number,
        'bit_offset': offset,
        'bit_interval_inclusive': [offset, offset + 16384 - 1],
        'offset_mod_12': offset % 12,
        'intersecting_code_interval_inclusive': [start, stop - 1],
        'intersecting_lanes': stop - start,
        'valid_raw_words': len(valid),
        'invalid_sentinel_words': stop - start - len(valid),
        'distinct_classes': len({classes[code] for code in valid}),
        'first_valid_examples': [
            {'code': code, 'directions': ''.join('ENWS'[d] for d in decode(code)),
             'class': classes[code], 'representative': representatives[classes[code]]}
            for code in valid[:3]],
    }

Path('check_results.json').write_text(json.dumps(summary, indent=2) + '\n')
print(json.dumps(summary, indent=2))
