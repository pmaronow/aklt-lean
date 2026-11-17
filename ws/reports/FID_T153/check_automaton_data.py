"""Read-only reconstruction of the supplied Lean literal tables and paper checks."""
from pathlib import Path
from collections import Counter
import hashlib
import json
import re

SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
source = SOURCE.read_text()
literals = {
    name: int(value, 16)
    for name, value in re.findall(
        r'^private noncomputable def (\w+) : ℕ := (0x[0-9a-f]+)$', source, re.M
    )
}


def parse_table(name):
    expression = re.search(r'^noncomputable def ' + name + r' : ℕ := (.*)$', source, re.M)[1]
    tokens = re.findall(r'<<<|\w+|[()+]', expression)
    assert ''.join(tokens) == re.sub(r'\s+', '', expression)
    position = 0

    def parse():
        nonlocal position
        token = tokens[position]
        position += 1
        if token == '(':
            left, offsets = parse()
            operator = tokens[position]
            position += 1
            right, right_offsets = parse()
            assert tokens[position] == ')'
            position += 1
            if operator == '<<<':
                assert not right_offsets
                return left << right, {key: offset + right for key, offset in offsets.items()}
            assert operator == '+' and not (offsets.keys() & right_offsets.keys())
            # Since supports do not overlap, addition really concatenates bits.
            assert left & right == 0
            return left + right, offsets | right_offsets
        if token.isdecimal():
            return int(token), {}
        return literals[token], {token: 0}

    packed, offsets = parse()
    assert position == len(tokens)
    return packed, offsets


tables = {name: parse_table(name) for name in ['rawClass', 'representatives', 'destinations', 'edgeKinds']}
raw_packed, raw_offsets = tables['rawClass']
assert len(raw_offsets) == 768
assert all(raw_offsets[f'rawClass_{i}'] == (767-i)*16384-4 for i in range(767))
assert raw_offsets['rawClass_767'] == 0
assert literals['rawClass_767'] < 1 << 16380
assert all(literals[f'rawClass_{i}'] < 1 << 16384 for i in range(768))
assert raw_packed.bit_length() <= 12 * 4**10


def lanes(packed, width, count):
    # Little-endian byte indexing avoids repeatedly shifting the entire table.
    data = packed.to_bytes((width*count+7)//8, 'little')
    mask = (1 << width)-1
    result = []
    for index in range(count):
        bit = width*index
        byte = bit//8
        span = (bit%8 + width + 7)//8
        result.append((int.from_bytes(data[byte:byte+span], 'little') >> (bit%8)) & mask)
    return result


raw = lanes(raw_packed, 12, 4**10)
representatives = lanes(tables['representatives'][0], 20, 3741)
destinations = lanes(tables['destinations'][0], 12, 3741*4)
kinds = lanes(tables['edgeKinds'][0], 2, 3741*4)
steps = [(1, 0), (0, 1), (-1, 0), (0, -1)]


def word(code, length=10):
    return tuple((code >> (2*(length-1-i))) & 3 for i in range(length))


def geometry(directions):
    vertex = (0, 0)
    vertices = [vertex]
    bonds = set()
    for direction in directions:
        dx, dy = steps[direction]
        next_vertex = (vertex[0]+dx, vertex[1]+dy)
        bond = tuple(sorted((vertex, next_vertex)))
        if bond in bonds:
            return None
        bonds.add(bond)
        vertex = next_vertex
        vertices.append(vertex)
    return vertices, bonds


# Independent paper recursion: append each of the four steps if its bond is new.
generated = {}
depth_counts = Counter()


def generate(length, code, vertex, bonds):
    depth_counts[length] += 1
    if length == 10:
        generated[code] = True
        return
    for direction, (dx, dy) in enumerate(steps):
        next_vertex = vertex[0]+dx, vertex[1]+dy
        bond = tuple(sorted((vertex, next_vertex)))
        if bond not in bonds:
            generate(length+1, code*4+direction, next_vertex, bonds | {bond})


generate(0, 0, (0, 0), set())
assert [depth_counts[i] for i in range(1,11)] == [4,12,36,108,316,916,2628,7500,21268,60092]
assert all(0 <= value <= 3741 for value in raw)
assert all((value < 3741) == (code in generated) for code, value in enumerate(raw))
assert all(0 <= code < 4**10 and code in generated and raw[code] == a
           for a, code in enumerate(representatives))
assert all(0 <= destination <= 3741 and ((destination == 0) == (kind == 3))
           for destination, kind in zip(destinations, kinds))

checked = 0
for code in generated:
    directions = word(code)
    vertices, bonds = geometry(directions)
    endpoint = vertices[-1]
    revisit = endpoint in vertices[:-1]
    a = raw[code]
    for direction, (dx, dy) in enumerate(steps):
        new_bond = tuple(sorted((endpoint, (endpoint[0]+dx, endpoint[1]+dy))))
        allowed = direction != (directions[-1]+2)%4 and new_bond not in bonds
        index = a*4+direction
        assert (destinations[index] != 0) == allowed, (code, direction, 'admissibility')
        if allowed:
            kind = 2 if revisit else (0 if direction == directions[-1] else 1)
            successor = ((code % 4**9)*4)+direction
            assert successor in generated
            assert kinds[index] == kind, (code, direction, 'kind')
            assert destinations[index]-1 == raw[successor], (code, direction, 'successor')
            if kind != 2:
                assert representatives[a]%4 == directions[-1], (code, direction, 'arrival')
        checked += 1

# Also compare totalized kinds on forbidden directions between class members.
for code in generated:
    directions = word(code)
    vertices, _ = geometry(directions)
    rep_directions = word(representatives[raw[code]])
    rep_vertices, _ = geometry(rep_directions)
    for d in range(4):
        k = 2 if vertices[-1] in vertices[:-1] else (0 if d == directions[-1] else 1)
        rep_k = 2 if rep_vertices[-1] in rep_vertices[:-1] else (0 if d == rep_directions[-1] else 1)
        assert k == rep_k, (code, d, 'total kind')

counts = Counter(kind for destination, kind in zip(destinations, kinds) if destination)
assert counts == {0:2516, 1:5032, 2:1872}

chunks = []
for number in range(730,735):
    offset = raw_offsets[f'rawClass_{number}']
    last_bit = offset+16383
    first_code, last_code = offset//12, last_bit//12
    complete = [code for code in range(first_code,last_code+1)
                if offset <= code*12 and code*12+11 <= last_bit]
    raw_codes = [code for code in range(first_code,last_code+1) if code in generated]
    chunk = {
        'name': f'rawClass_{number}', 'source_line': 15+2*number,
        'bit_offset': offset, 'last_bit': last_bit,
        'first_code': first_code, 'last_code': last_code,
        'complete_lanes': len(complete),
        'raw_codes_intersected': len(raw_codes),
        'invalid_codes_intersected': last_code-first_code+1-len(raw_codes),
        'raw_class_ids': sorted({raw[code] for code in raw_codes}),
        'sha256_of_2048_little_endian_bytes': hashlib.sha256(
            literals[f'rawClass_{number}'].to_bytes(2048,'little')).hexdigest(),
    }
    for code in range(first_code,last_code+1):
        assert (geometry(word(code)) is not None) == (code in generated)
    chunks.append(chunk)

# Try the natural textual archive representation, without accessing the archive.
lines = ['60092 3741']
lines += [f'{code} {raw[code]}' for code in sorted(generated)]
for a, representative in enumerate(representatives):
    lines.append(' '.join(map(str, [representative] +
        [destinations[a*4+d]-1 for d in range(4)] +
        [kinds[a*4+d] if destinations[a*4+d] else -1 for d in range(4)])))
archive_text = '\n'.join(lines)+'\n'
reconstructed_sha = hashlib.sha256(archive_text.encode()).hexdigest()
claimed_sha = re.search(r'Archive SHA-256: ([0-9a-f]+)',source)[1]
results = {
    'status': 'all assertions passed',
    'literal_count':len(literals),
    'raw_chunk_count':len(raw_offsets),
    'raw_cardinality':len(generated),
    'depth_counts':[depth_counts[i] for i in range(1,11)],
    'all_codes_checked':len(raw),
    'raw_direction_comparisons':checked,
    'edge_counts':dict(counts),
    'reconstructed_archive_sha256':reconstructed_sha,
    'archive_sha_matches_source_comment':reconstructed_sha == claimed_sha,
    'chunks':chunks,
}
Path('check_results.json').write_text(json.dumps(results,indent=2)+'\n')
print(json.dumps(results,indent=2))
