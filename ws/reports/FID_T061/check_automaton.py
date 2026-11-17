"""Independent finite reconstruction of the supplied Lean literal quotient.

Reads only the designated Lean input.  No archived data or generator is used.
"""
import ast
from collections import Counter
import hashlib
import json
from pathlib import Path
import re

ROOT = Path('/home/ubuntu/aklt/review/FID_T/lean')
SOURCE = ROOT / 'AKLT/Defs/Automaton10Data.lean'
text = SOURCE.read_text()
lines = text.splitlines()
literal_re = re.compile(
    r'private noncomputable def (\w+) : ℕ := 0x([0-9a-f]+)$')
literals = {}
literal_lines = {}
hexes = {}
for line_number, line in enumerate(lines, 1):
    match = literal_re.fullmatch(line)
    if match:
        name, digits = match.groups()
        literals[name] = int(digits, 16)
        literal_lines[name] = line_number
        hexes[name] = digits


def placements(node, offset=0):
    """Flatten exact parenthesized sums and shifts to leaf bit offsets."""
    if isinstance(node, ast.Name):
        return [(node.id, offset)]
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add):
        return placements(node.left, offset) + placements(node.right, offset)
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.LShift):
        assert isinstance(node.right, ast.Constant)
        return placements(node.left, offset + node.right.value)
    raise AssertionError(ast.dump(node))


def packed_table(name, width, count):
    line = next(l for l in lines if l.startswith(f'noncomputable def {name} : ℕ := '))
    expr = line.split(' := ', 1)[1].replace('<<<', '<<')
    leaves = placements(ast.parse(expr, mode='eval').body)
    assert len({leaf for leaf, _ in leaves}) == len(leaves)
    assert {leaf for leaf, _ in leaves} == {
        key for key in literals if key.startswith(name + '_')}
    ordered = sorted(leaves, key=lambda pair: pair[1])
    assert ordered[0][1] == 0
    for (leaf, offset), (_, next_offset) in zip(ordered, ordered[1:]):
        assert literals[leaf] < 2 ** (next_offset - offset)
        assert len(hexes[leaf]) * 4 == next_offset - offset
    top, top_offset = ordered[-1]
    assert literals[top].bit_length() + top_offset <= width * count
    number = sum(literals[leaf] << offset for leaf, offset in leaves)
    data = number.to_bytes((width * count + 7) // 8, 'little')

    def lane(index):
        bit = width * index
        first = bit // 8
        return (int.from_bytes(data[first:first + (width + 14) // 8], 'little')
                >> (bit % 8)) & ((1 << width) - 1)

    values = [lane(i) for i in range(count)]
    # Independent hex extraction cross-check, including each split boundary.
    digits = format(number, 'x').zfill((width * count + 3) // 4)
    if width % 4 == 0:
        size = width // 4
        assert values == [int(digits[i:i + size], 16)
                          for i in range(len(digits) - size, -1, -size)]
    return values, dict(leaves)


raw, raw_offsets = packed_table('rawClass', 12, 4 ** 10)
representatives, _ = packed_table('representatives', 20, 3741)
destinations, _ = packed_table('destinations', 12, 4 * 3741)
kinds, _ = packed_table('edgeKinds', 2, 4 * 3741)

STEPS = ((1, 0), (0, 1), (-1, 0), (0, -1))


def decode(code):
    return tuple((code >> (2 * (9 - i))) & 3 for i in range(10))


def geometry(word):
    vertices = [(0, 0)]
    bonds = set()
    for direction in word:
        x, y = vertices[-1]
        dx, dy = STEPS[direction]
        end = (x + dx, y + dy)
        bond = frozenset((vertices[-1], end))
        if bond in bonds:
            return None
        bonds.add(bond)
        vertices.append(end)
    return vertices, bonds


counts = [0] * 11
raw_words = {}


def generate(depth=0, code=0, vertices=((0, 0),), bonds=frozenset()):
    counts[depth] += 1
    if depth == 10:
        raw_words[code] = (vertices, bonds)
        return
    x, y = vertices[-1]
    for d, (dx, dy) in enumerate(STEPS):
        end = (x + dx, y + dy)
        bond = frozenset((vertices[-1], end))
        if bond not in bonds:
            generate(depth + 1, 4 * code + d,
                     vertices + (end,), bonds | {bond})


generate()
assert counts[1:] == [4, 12, 36, 108, 316, 916, 2628, 7500, 21268, 60092]
coverage_errors = [code for code, label in enumerate(raw)
                   if label > 3741 or ((label < 3741) != (code in raw_words))]
assert not coverage_errors, coverage_errors[:10]
representative_errors = [a for a, code in enumerate(representatives)
                         if code >= 4 ** 10 or code not in raw_words or raw[code] != a]
assert not representative_errors, representative_errors[:10]


def row(code, geom):
    vertices, bonds = geom
    endpoint = vertices[-1]
    arrival = code % 4
    revisit = endpoint in vertices[:-1]
    result = []
    for d, (dx, dy) in enumerate(STEPS):
        end = (endpoint[0] + dx, endpoint[1] + dy)
        allowed = d != (arrival + 2) % 4 and frozenset((endpoint, end)) not in bonds
        # Kinds are also compared for inadmissible directions in the paper.
        kind = 2 if revisit else (0 if d == arrival else 1)
        successor_code = ((code % (4 ** 9)) * 4 + d)
        result.append((allowed, kind, raw[successor_code] if allowed else None))
    return result


representative_rows = [row(code, raw_words[code]) for code in representatives]
transition_errors = []
paper_kind_errors = []
for code, geom in raw_words.items():
    a = raw[code]
    regenerated = row(code, geom)
    for d, (allowed, kind, successor) in enumerate(regenerated):
        i = 4 * a + d
        representative_row = representative_rows[a][d]
        if kind != representative_row[1]:
            paper_kind_errors.append((code, a, d))
        if not (allowed == (destinations[i] != 0)
                and destinations[i] <= 3741
                and ((destinations[i] == 0) == (kinds[i] == 3))
                and (not allowed or (kinds[i] == kind
                                     and destinations[i] - 1 == successor))
                and (not allowed or kind == 2
                     or representatives[a] % 4 == code % 4)):
            transition_errors.append((code, a, d))
assert not transition_errors, transition_errors[:10]
assert not paper_kind_errors, paper_kind_errors[:10]
edge_counts = Counter(kinds[i] for i, dest in enumerate(destinations) if dest != 0)
assert edge_counts == Counter({0: 2516, 1: 5032, 2: 1872}), edge_counts

targets = []
for k in range(270, 275):
    name = f'rawClass_{k}'
    offset = raw_offsets[name]
    width = len(hexes[name]) * 4
    first = offset // 12
    last = (offset + width - 1) // 12
    affected = [code for code in range(first, last + 1) if code in raw_words]
    complete = [code for code in range(first, last + 1)
                if offset <= 12 * code and 12 * (code + 1) <= offset + width]
    raw_complete = [code for code in complete if code in raw_words]
    sample = next(iter(raw_complete), None)
    targets.append({
        'declaration': name,
        'line': literal_lines[name],
        'hex_digits': len(hexes[name]),
        'literal_sha256': hashlib.sha256(hexes[name].encode()).hexdigest(),
        'bit_offset': offset,
        'bit_width': width,
        'code_first': first,
        'code_last': last,
        'first_lane_bit_offset': offset % 12,
        'end_lane_bit_offset': (offset + width) % 12,
        'affected_lanes': last - first + 1,
        'affected_raw_windows': len(affected),
        'fully_contained_lanes': len(complete),
        'fully_contained_raw_windows': len(raw_complete),
        'affected_invalid_words': last - first + 1 - len(affected),
        'distinct_classes': len({raw[code] for code in affected}),
        'sample_code': sample,
        'sample_word_ENWS': ''.join('ENWS'[d] for d in decode(sample)) if sample is not None else None,
        'sample_class': raw[sample] if sample is not None else None,
        'sample_representative_code': representatives[raw[sample]] if sample is not None else None,
    })

results = {
    'raw_class_chunks': len(raw_offsets),
    'independent_raw_counts': counts[1:],
    'raw_coverage_checked': len(raw),
    'coverage_errors': len(coverage_errors),
    'representatives_checked': len(representatives),
    'representative_errors': len(representative_errors),
    'raw_labelled_transitions_checked': 4 * len(raw_words),
    'transition_errors': len(transition_errors),
    'paper_kind_errors_including_inadmissible': len(paper_kind_errors),
    'quotient_edge_counts': dict(edge_counts),
    'targets': targets,
}
Path('check_results.json').write_text(json.dumps(results, indent=2) + '\n')
print(json.dumps(results, indent=2))
