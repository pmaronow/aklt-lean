"""Read-only reconstruction of the memory-ten finite contract.

Inputs are restricted to the assigned Lean file. Geometry and the recursion are
transcribed from app-input-contracts.tex, definitions d:memory-automaton and
p:automaton10. No Lean execution or external archive is used.
"""

from array import array
import ast
from collections import Counter
import hashlib
import json
from pathlib import Path
import re


ROOT = Path('/home/ubuntu/aklt/reports/FID_T098')
SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
source = SOURCE.read_text()
literal_matches = list(re.finditer(
    r'^private noncomputable def (\w+) : ℕ := 0x([0-9a-f]+)$', source, re.M))
hexes = {m[1]: m[2] for m in literal_matches}
line_numbers = {m[1]: source.count('\n', 0, m.start()) + 1 for m in literal_matches}
assert len(hexes) == 786


def assembly_offsets(node, shift=0):
    if isinstance(node, ast.Name):
        return [(node.id, shift)]
    assert isinstance(node, ast.BinOp)
    if isinstance(node.op, ast.Add):
        return assembly_offsets(node.left, shift) + assembly_offsets(node.right, shift)
    assert isinstance(node.op, ast.LShift)
    assert isinstance(node.right, ast.Constant) and isinstance(node.right.value, int)
    return assembly_offsets(node.left, shift + node.right.value)


def read_assembly(name):
    expression = re.search(rf'^noncomputable def {name} : ℕ := (.*)$', source, re.M)[1]
    terms = assembly_offsets(ast.parse(expression.replace('<<<', '<<'), mode='eval').body)
    offsets = dict(terms)
    assert len(offsets) == len(terms)
    assert set(offsets) == {n for n in hexes if n.startswith(name + '_')}
    intervals = sorted((o, o + len(hexes[n]) * 4) for n, o in terms)
    assert intervals[0][0] == 0
    assert all(a[1] == b[0] for a, b in zip(intervals, intervals[1:]))
    value = sum(int(hexes[n], 16) << o for n, o in terms)
    return value, offsets


packed = {}
offsets = {}
for table in ('rawClass', 'representatives', 'destinations', 'edgeKinds'):
    packed[table], offsets[table] = read_assembly(table)

# Extract two 12-bit lanes per three bytes, avoiding a million large shifts.
raw_bytes = packed['rawClass'].to_bytes(12 * 4**10 // 8, 'little')
classes = array('H')
for i in range(0, len(raw_bytes), 3):
    pair = int.from_bytes(raw_bytes[i:i+3], 'little')
    classes.append(pair & 4095)
    classes.append(pair >> 12)


def lanes(table, width, count):
    value = packed[table]
    mask = (1 << width) - 1
    return [(value >> (width * i)) & mask for i in range(count)]


representatives = lanes('representatives', 20, 3741)
destinations = lanes('destinations', 12, 3741 * 4)
kinds = lanes('edgeKinds', 2, 3741 * 4)
assert max(classes) <= 3741
assert max(representatives) < 4**10
assert max(destinations) <= 3741
assert all((dest == 0) == (kind == 3) for dest, kind in zip(destinations, kinds))

STEPS = ((1, 0), (0, 1), (-1, 0), (0, -1))
seen = bytearray(4**10)
depth_counts = [0] * 11
vertices = [(0, 0)]
used_bonds = set()
word = []
raw_rows = {}
transition_checks = 0
admitted_checks = 0
nonrevisit_arrival_checks = 0


def bond(x, y):
    # Finset {x,y}: sorting forgets orientation, and the unit step excludes x=y.
    return tuple(sorted((x, y)))


def generate(depth=0, code=0):
    global transition_checks, admitted_checks, nonrevisit_arrival_checks
    depth_counts[depth] += 1
    x = vertices[-1]
    if depth == 10:
        assert not seen[code], ('duplicate code', code)
        seen[code] = 1
        a = classes[code]
        assert a < 3741, ('missing raw word', code, a)
        raw_rows[code] = a
        revisit = x in vertices[:-1]
        last = word[-1]
        for d, step in enumerate(STEPS):
            y = (x[0] + step[0], x[1] + step[1])
            admissible = d != (last + 2) % 4 and bond(x, y) not in used_bonds
            row = 4 * a + d
            transition_checks += 1
            assert (destinations[row] != 0) == admissible, ('admissibility', code, a, d)
            if admissible:
                admitted_checks += 1
                kind = 2 if revisit else (0 if d == last else 1)
                assert kinds[row] == kind, ('kind', code, a, d)
                successor_code = (code % 4**9) * 4 + d
                assert destinations[row] - 1 == classes[successor_code], ('successor', code, a, d)
                if kind != 2:
                    nonrevisit_arrival_checks += 1
                    assert representatives[a] % 4 == last, ('arrival', code, a, d)
        return
    for d, step in enumerate(STEPS):
        y = (x[0] + step[0], x[1] + step[1])
        edge = bond(x, y)
        if edge in used_bonds:
            continue
        used_bonds.add(edge)
        vertices.append(y)
        word.append(d)
        generate(depth + 1, code * 4 + d)
        word.pop()
        vertices.pop()
        used_bonds.remove(edge)


generate()
assert depth_counts == [1, 4, 12, 36, 108, 316, 916, 2628, 7500, 21268, 60092]
assert all((classes[code] < 3741) == bool(seen[code]) for code in range(4**10))
assert all(raw_rows.get(rep) == a for a, rep in enumerate(representatives))
edge_counts = Counter(kind for dest, kind in zip(destinations, kinds) if dest)
assert edge_counts == {0: 2516, 1: 5032, 2: 1872}


def word_string(code):
    return ''.join('ENWS'[(code >> (2 * (9-i))) & 3] for i in range(10))


def decode_vertices(code):
    points = [(0, 0)]
    edges = []
    for i in range(10):
        d = (code >> (2 * (9-i))) & 3
        s = STEPS[d]
        x = points[-1]
        y = (x[0] + s[0], x[1] + s[1])
        points.append(y)
        edges.append(bond(x, y))
    return points, edges


assigned = []
for i in range(455, 460):
    name = f'rawClass_{i}'
    low = offsets['rawClass'][name]
    high = low + 4 * len(hexes[name]) - 1
    start, end = low // 12, high // 12
    live = [code for code in range(start, end+1) if seen[code]]
    full_start, full_end = (low + 11) // 12, (high - 11) // 12
    boundaries = [c for c in (start, end) if c < full_start or c > full_end]
    samples = []
    for code in sorted(set(boundaries + live[:3] + live[-3:])):
        pts, edges = decode_vertices(code)
        repeated = [(j, k) for j in range(10) for k in range(j+1, 10) if edges[j] == edges[k]]
        a = classes[code]
        samples.append({
            'code': code, 'word': word_string(code), 'class': a,
            'raw': bool(seen[code]), 'repeated_bond_indices_zero_based': repeated,
            'representative_code': representatives[a] if a < 3741 else None,
            'representative_word': word_string(representatives[a]) if a < 3741 else None,
        })
    item = {
        'name': name, 'line': line_numbers[name], 'hex_digits': len(hexes[name]),
        'bit_interval_inclusive': [low, high], 'intersecting_codes_inclusive': [start, end],
        'complete_codes_inclusive': [full_start, full_end],
        'raw_codes_intersecting': len(live), 'invalid_codes_intersecting': end-start+1-len(live),
        'distinct_raw_classes_intersecting': len({classes[c] for c in live}),
        'hex_sha256': hashlib.sha256(hexes[name].encode()).hexdigest(),
        'samples': samples,
    }
    assigned.append(item)

# Reconstruct the specified text layout. A hash mismatch would merely mean that
# the archive's whitespace/formatting is unavailable in these read-only inputs.
archive_text = f'{len(raw_rows)} 3741\n'
archive_text += ''.join(f'{code} {a}\n' for code, a in raw_rows.items())
for a, rep in enumerate(representatives):
    ds = [destinations[4*a+d]-1 for d in range(4)]
    ks = [kinds[4*a+d] if destinations[4*a+d] else -1 for d in range(4)]
    archive_text += ' '.join(map(str, [rep] + ds + ks)) + '\n'
archive_sha256 = hashlib.sha256(archive_text.encode()).hexdigest()
stated_sha256 = re.search(r'Archive SHA-256: ([a-f0-9]{64})', source)[1]
results = {
    'result': 'PASS', 'depth_counts': depth_counts,
    'all_raw_code_coverage_checks': len(classes),
    'raw_to_quotient_direction_checks': transition_checks,
    'admitted_kind_and_successor_checks': admitted_checks,
    'nonrevisit_arrival_checks': nonrevisit_arrival_checks,
    'representative_checks': len(representatives),
    'edge_counts_straight_turn_revisit': dict(edge_counts),
    'raw_class_table_bit_length': packed['rawClass'].bit_length(),
    'reconstructed_archive_sha256': archive_sha256,
    'archive_hash_matches_docstring': archive_sha256 == stated_sha256,
    'assigned': assigned,
}
(ROOT / 'check_results.json').write_text(json.dumps(results, indent=2) + '\n')
print(json.dumps(results, indent=2))
