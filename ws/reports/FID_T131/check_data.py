"""Independent reconstruction using only the permitted Lean and paper inputs.

This is an arithmetic/finite-model check, not a Lean proof.
Run with: python3 check_data.py
"""
from pathlib import Path
import ast
import collections
import hashlib
import json
import re

SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
source = SOURCE.read_text()
literals = {
    name: int(value, 16)
    for name, value in re.findall(
        r'^private noncomputable def (\w+) : ℕ := (0x[0-9a-f]+)$',
        source, re.M,
    )
}


def assembly(name):
    expression = re.search(
        rf'^noncomputable def {name} : ℕ := (.+)$', source, re.M
    ).group(1)
    tree = ast.parse(expression.replace('<<<', '<<'), mode='eval').body

    def visit(node):
        if isinstance(node, ast.Name):
            return literals[node.id], {node.id: 0}
        assert isinstance(node, ast.BinOp)
        left, locations = visit(node.left)
        if isinstance(node.op, ast.LShift):
            assert isinstance(node.right, ast.Constant)
            shift = node.right.value
            return left << shift, {key: pos + shift for key, pos in locations.items()}
        assert isinstance(node.op, ast.Add)
        right, others = visit(node.right)
        assert not locations.keys() & others.keys()
        # Addition really concatenates disjoint fields: no carry may alter data.
        assert left & right == 0
        return left + right, locations | others

    value, locations = visit(tree)
    return value, locations


def lanes(value, width, count):
    data = value.to_bytes((width * count + 7) // 8, 'little')
    mask = (1 << width) - 1
    result = []
    for index in range(count):
        bit = width * index
        first_byte, remainder = divmod(bit, 8)
        end = (bit + width + 7) // 8
        result.append((int.from_bytes(data[first_byte:end], 'little') >> remainder) & mask)
    return result


packed, positions = assembly('rawClass')
assert len(positions) == 768
literal_widths = {
    name: 4*len(value[2:])
    for name, value in re.findall(
        r'^private noncomputable def (\w+) : ℕ := (0x[0-9a-f]+)$',
        source, re.M,
    )
}
next_bit = 0
for j in reversed(range(768)):
    name = f'rawClass_{j}'
    assert positions[name] == next_bit
    assert literals[name] < 1 << literal_widths[name]
    next_bit += literal_widths[name]
assert next_bit <= 12*4**10
raw_class = lanes(packed, 12, 4**10)
representatives = lanes(assembly('representatives')[0], 20, 3741)
destinations = lanes(assembly('destinations')[0], 12, 4*3741)
kinds = lanes(assembly('edgeKinds')[0], 2, 4*3741)

STEPS = ((1, 0), (0, 1), (-1, 0), (0, -1))


def bond(x, y):
    return tuple(sorted((x, y)))


raw = set()
depth_counts = [0]*11


def generate(depth, code, endpoint, used):
    depth_counts[depth] += 1
    if depth == 10:
        raw.add(code)
        return
    for d, step in enumerate(STEPS):
        following = endpoint[0]+step[0], endpoint[1]+step[1]
        edge = bond(endpoint, following)
        if edge not in used:
            used.add(edge)
            generate(depth+1, 4*code+d, following, used)
            used.remove(edge)


generate(0, 0, (0, 0), set())
assert depth_counts[1:] == [4, 12, 36, 108, 316, 916, 2628, 7500, 21268, 60092]
assert len(raw) == 60092
assert all(value <= 3741 for value in raw_class)
assert {code for code, value in enumerate(raw_class) if value < 3741} == raw
assert all(code in raw and raw_class[code] == a for a, code in enumerate(representatives))
assert all(0 <= code < 4**10 for code in representatives)
assert all(0 <= destination <= 3741 for destination in destinations)
assert all((destination == 0) == (kind == 3) for destination, kind in zip(destinations, kinds))


def geometry(code):
    word = tuple((code >> (2*(9-j))) & 3 for j in range(10))
    vertices = [(0, 0)]
    used = set()
    for d in word:
        x, y = vertices[-1]
        dx, dy = STEPS[d]
        following = x+dx, y+dy
        used.add(bond(vertices[-1], following))
        vertices.append(following)
    endpoint = vertices[-1]
    revisit = endpoint in vertices[:-1]
    allowed = []
    detected_kinds = []
    for d, (dx, dy) in enumerate(STEPS):
        allowed.append(d != (word[-1]+2) % 4 and
                       bond(endpoint, (endpoint[0]+dx, endpoint[1]+dy)) not in used)
        detected_kinds.append(2 if revisit else (0 if d == word[-1] else 1))
    return word[-1], tuple(allowed), tuple(detected_kinds)


representative_geometry = [geometry(code) for code in representatives]
checks = collections.Counter()
for code in sorted(raw):
    a = raw_class[code]
    arrival, allowed, detected_kinds = geometry(code)
    rep_arrival, rep_allowed, rep_kinds = representative_geometry[a]
    assert allowed == rep_allowed
    # The paper compares kind even for directions that are not admitted.
    assert detected_kinds == rep_kinds
    for d in range(4):
        index = 4*a+d
        assert (destinations[index] != 0) == allowed[d]
        checks['raw_direction_comparisons'] += 1
        if allowed[d]:
            successor = (code % 4**9)*4+d
            assert successor in raw
            assert kinds[index] == detected_kinds[d]
            assert destinations[index]-1 == raw_class[successor]
            if detected_kinds[d] != 2:
                assert arrival == rep_arrival
            checks['admissible_raw_edges'] += 1

edge_counts = collections.Counter(
    kind for destination, kind in zip(destinations, kinds) if destination != 0
)
assert dict(edge_counts) == {0: 2516, 1: 5032, 2: 1872}

chunk_results = []
for j in range(620, 625):
    name = f'rawClass_{j}'
    low_bit = positions[name]
    high_bit = low_bit+16384-1
    first, last = low_bit//12, high_bit//12
    affected = range(first, last+1)
    valid = [code for code in affected if code in raw]
    affected_classes = sorted({raw_class[code] for code in valid})
    split_boundaries = []
    for boundary in (low_bit, high_bit+1):
        if boundary % 12:
            code = boundary//12
            split_boundaries.append({'code': code, 'value': raw_class[code],
                                     'raw': code in raw, 'low_part_bits': boundary % 12})
    # Directly verify this literal's bits against the reconstructed lane values,
    # including the lane fragments at either end.
    expected_bits = 0
    for code in affected:
        start, stop = max(12*code, low_bit), min(12*(code+1), high_bit+1)
        fragment = (raw_class[code] >> (start-12*code)) & ((1 << (stop-start))-1)
        expected_bits |= fragment << (start-low_bit)
    assert literals[name] == expected_bits
    chunk_results.append({
        'name': name,
        'line': next(i for i, line in enumerate(source.splitlines(), 1)
                     if line.startswith(f'private noncomputable def {name} ')),
        'bit_range_inclusive': [low_bit, high_bit],
        'word_code_range_inclusive': [first, last],
        'raw_words': len(valid),
        'nonraw_words': len(affected)-len(valid),
        'class_count': len(affected_classes),
        'class_range': [min(affected_classes), max(affected_classes)] if affected_classes else None,
        'split_boundaries': split_boundaries,
        'sample_raw_codes_and_classes': [(code, raw_class[code]) for code in valid[:3]],
    })

result = {
    'source_sha256': hashlib.sha256(source.encode()).hexdigest(),
    'raw_windows_by_length': depth_counts[1:],
    'raw_class_range': [min(raw_class[code] for code in raw), max(raw_class[code] for code in raw)],
    'class_count': len(set(raw_class[code] for code in raw)),
    'nonraw_sentinel': list(set(raw_class[code] for code in range(4**10) if code not in raw)),
    'checks': dict(checks),
    'quotient_edge_counts': dict(sorted(edge_counts.items())),
    'chunks': chunk_results,
    'result': 'all assertions passed',
}
Path('check_results.json').write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps(result, indent=2))
