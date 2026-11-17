"""Read-only mathematical reconstruction of the supplied Lean literal tables.

No archive, export script, or non-input repository file is read.  This check
evaluates the literal shift/add expressions and regenerates the paper's trails.
"""

import ast
from collections import Counter
import hashlib
import json
from pathlib import Path
import re


SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
text = SOURCE.read_text()
values = {}
expressions = {}
line_numbers = {}
literal_sizes = {}
for line_number, line in enumerate(text.splitlines(), 1):
    match = re.fullmatch(r'(private )?noncomputable def (\w+) : ℕ := (.+)', line)
    if match:
        name, expression = match[2], match[3]
        line_numbers[name] = line_number
        if expression.startswith('0x'):
            assert re.fullmatch(r'0x[0-9a-f]+', expression)
            values[name] = int(expression, 16)
            literal_sizes[name] = len(expression[2:]) * 4
        else:
            expressions[name] = ast.parse(expression.replace('<<<', '<<'), mode='eval').body


def evaluate(node):
    if isinstance(node, ast.Name):
        return values[node.id]
    if isinstance(node, ast.Constant) and isinstance(node.value, int):
        return node.value
    assert isinstance(node, ast.BinOp)
    left, right = evaluate(node.left), evaluate(node.right)
    if isinstance(node.op, ast.Add):
        return left + right
    assert isinstance(node.op, ast.LShift)
    return left << right


def pieces(node, offset=0):
    if isinstance(node, ast.Name):
        return [(node.id, offset)]
    assert isinstance(node, ast.BinOp)
    if isinstance(node.op, ast.Add):
        return pieces(node.left, offset) + pieces(node.right, offset)
    assert isinstance(node.op, ast.LShift)
    return pieces(node.left, offset + evaluate(node.right))


table_widths = {'rawClass': (12, 4**10), 'representatives': (20, 3741),
                'destinations': (12, 3741*4), 'edgeKinds': (2, 3741*4)}
tables = {}
offsets = {}
allocated_widths = {}
for name, expression in expressions.items():
    values[name] = evaluate(expression)
    width, count = table_widths[name]
    component_list = pieces(expression)
    offsets.update(dict(component_list))
    # Verify the exact expression is a nonoverlapping, gap-free concatenation.
    components = sorted(component_list, key=lambda component: component[1])
    assert components[0][1] == 0
    assert len(set(component[0] for component in components)) == len(components)
    for i, (component, offset) in enumerate(components):
        next_offset = components[i+1][1] if i+1 < len(components) else width*count
        assert values[component].bit_length() <= next_offset - offset
        assert literal_sizes[component] <= next_offset - offset
        allocated_widths[component] = next_offset - offset
        if name == 'rawClass':
            chunk_index = int(component.rsplit('_', 1)[1])
            assert offset == (0 if chunk_index == 767 else (767-chunk_index)*16384-4)
    packed_bytes = values[name].to_bytes((width*count + 7)//8, 'little')
    lanes = []
    for i in range(count):
        bit = i*width
        start = bit//8
        lane_bytes = packed_bytes[start:(bit + width + 7)//8]
        lanes.append((int.from_bytes(lane_bytes, 'little') >> (bit % 8)) & ((1 << width)-1))
    tables[name] = lanes

raw = tables['rawClass']
representatives = tables['representatives']
destinations = tables['destinations']
kinds = tables['edgeKinds']
assert len(raw) == 4**10
assert max(raw) == 3741
assert all(code < 4**10 for code in representatives)
assert all(0 <= destination <= 3741 for destination in destinations)
assert all((destination == 0) == (kind == 3)
           for destination, kind in zip(destinations, kinds))

steps = ((1, 0), (0, 1), (-1, 0), (0, -1))
raw_states = {}
depth_counts = Counter()


def bond(a, b):
    return tuple(sorted((a, b)))


def generate(code=0, directions=(), vertices=((0, 0),), bonds=frozenset()):
    depth_counts[len(directions)] += 1
    if len(directions) == 10:
        endpoint = vertices[-1]
        admitted = []
        for d, (dx, dy) in enumerate(steps):
            new_vertex = endpoint[0]+dx, endpoint[1]+dy
            admitted.append(d != ((directions[-1]+2) % 4)
                            and bond(endpoint, new_vertex) not in bonds)
        revisit = endpoint in vertices[:-1]
        detected_kinds = tuple(2 if revisit else (0 if d == directions[-1] else 1)
                               for d in range(4))
        raw_states[code] = tuple(admitted), detected_kinds, directions[-1]
        return
    endpoint = vertices[-1]
    for d, (dx, dy) in enumerate(steps):
        new_vertex = endpoint[0]+dx, endpoint[1]+dy
        new_bond = bond(endpoint, new_vertex)
        if new_bond not in bonds:
            generate(4*code+d, directions+(d,), vertices+(new_vertex,), bonds | {new_bond})


generate()
assert [depth_counts[i] for i in range(1, 11)] == [4,12,36,108,316,916,2628,7500,21268,60092]
assert {code for code, cls in enumerate(raw) if cls < 3741} == set(raw_states)
assert len(set(representatives)) == 3741
for cls, representative in enumerate(representatives):
    assert representative in raw_states
    assert raw[representative] == cls

edge_counts = Counter()
for cls, representative in enumerate(representatives):
    admitted, detected_kinds, arrival = raw_states[representative]
    assert arrival == representative % 4
    for d in range(4):
        i = cls*4+d
        assert admitted[d] == (destinations[i] != 0)
        if admitted[d]:
            successor_code = ((representative % (4**9))*4)+d
            assert successor_code in raw_states
            assert destinations[i]-1 == raw[successor_code]
            assert kinds[i] == detected_kinds[d]
            edge_counts[kinds[i]] += 1
assert edge_counts == Counter({0:2516, 1:5032, 2:1872})

for code, (admitted, detected_kinds, arrival) in raw_states.items():
    cls = raw[code]
    rep_admitted, rep_kinds, rep_arrival = raw_states[representatives[cls]]
    assert admitted == rep_admitted
    assert detected_kinds == rep_kinds  # Also checks kinds on forbidden directions.
    for d in range(4):
        if admitted[d]:
            successor_code = ((code % (4**9))*4)+d
            assert successor_code in raw_states
            assert raw[successor_code] == destinations[cls*4+d]-1
            if detected_kinds[d] != 2:
                assert arrival == rep_arrival

chunk_results = []
for j in range(555, 560):
    name = f'rawClass_{j}'
    offset = offsets[name]
    width = allocated_widths[name]
    first = offset//12
    last = (offset+width-1)//12
    affected = range(first, last+1)
    valid_codes = [code for code in affected if code in raw_states]
    assert offset == (767-j)*16384-4
    assert width == 16384
    # Reconstruct this exact private natural from verified lanes, including
    # both partial lanes if the chunk cuts across the 12-bit lane boundaries.
    reconstructed = sum(raw[code] << (12*(code-first)) for code in affected)
    reconstructed = (reconstructed >> (offset - first*12)) & ((1 << width)-1)
    assert reconstructed == values[name]
    chunk_results.append({
        'name': name, 'source_line': line_numbers[name],
        'bit_range_inclusive': [offset, offset+width-1],
        'code_range_inclusive': [first, last],
        'affected_lanes': last-first+1,
        'raw_lanes': len(valid_codes), 'invalid_lanes': last-first+1-len(valid_codes),
        'distinct_valid_classes': len({raw[code] for code in valid_codes}),
        'first_lane': raw[first], 'last_lane': raw[last],
        'little_endian_2048_byte_sha256': hashlib.sha256(values[name].to_bytes(2048, 'little')).hexdigest(),
    })

result = {
    'checked_source_sha256': hashlib.sha256(text.encode()).hexdigest(),
    'parsed_literal_count': len(literal_sizes),
    'checked_raw_codes': len(raw), 'regenerated_raw_windows': len(raw_states),
    'invalid_codes': len(raw)-len(raw_states),
    'regenerated_counts_by_depth': dict(sorted(depth_counts.items())),
    'checked_representatives': len(representatives),
    'checked_raw_direction_comparisons': 4*len(raw_states),
    'edge_counts': dict(edge_counts),
    'chunks': chunk_results,
    'result': 'all assertions passed',
}
Path('check_data_results.json').write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps(result, indent=2))
