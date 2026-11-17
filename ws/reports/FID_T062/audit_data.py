"""Read-only reconstruction of the paper's memory-ten finite data contract."""
import ast
from collections import Counter
import hashlib
from pathlib import Path
import re

SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
text = SOURCE.read_text()
literals = {}
line_numbers = {}
hex_text = {}
for line_number, line in enumerate(text.splitlines(), 1):
    match = re.fullmatch(r'private noncomputable def (\w+) : ℕ := (0x[0-9a-fA-F]+)', line)
    if match:
        name, value = match.groups()
        literals[name] = int(value, 16)
        line_numbers[name] = line_number
        hex_text[name] = value


def parse_table(name):
    expression = re.search(r'^noncomputable def ' + name + r' : ℕ := (.*)$', text, re.M)[1]

    def visit(node):
        if isinstance(node, ast.Name):
            return literals[node.id], [(node.id, 0)]
        assert isinstance(node, ast.BinOp)
        left, terms = visit(node.left)
        if isinstance(node.op, ast.LShift):
            assert isinstance(node.right, ast.Constant) and isinstance(node.right.value, int)
            shift = node.right.value
            assert shift >= 0
            return left << shift, [(name, offset + shift) for name, offset in terms]
        assert isinstance(node.op, ast.Add)
        right, other_terms = visit(node.right)
        assert left & right == 0, 'Unexpected carry between packed literal pieces'
        return left + right, terms + other_terms

    value, terms = visit(ast.parse(expression.replace('<<<', '<<'), mode='eval').body)
    names = [piece for piece, _ in terms]
    assert len(names) == len(set(names))
    assert set(names) == {piece for piece in literals if piece.startswith(name + '_')}
    ordered = sorted(terms, key=lambda term: term[1])
    for (piece, offset), (_, next_offset) in zip(ordered, ordered[1:]):
        assert literals[piece] < 1 << (next_offset - offset)
    print(f'TABLE {name}: {len(terms)} pieces, {value.bit_length()} significant bits, all pieces present once, no overlap/carry')
    return value, dict(terms)


packed, offsets = {}, {}
for name in ('rawClass', 'representatives', 'destinations', 'edgeKinds'):
    packed[name], offsets[name] = parse_table(name)

N = 4 ** 10
raw_bytes = packed['rawClass'].to_bytes((N * 12 + 7) // 8, 'little')
raw = []
for byte_index in range(0, len(raw_bytes), 3):
    pair = int.from_bytes(raw_bytes[byte_index:byte_index + 3], 'little')
    raw.extend((pair & 4095, pair >> 12))
assert len(raw) == N


def lane(name, width, index):
    return (packed[name] >> (width * index)) & ((1 << width) - 1)


STEPS = ((1, 0), (0, 1), (-1, 0), (0, -1))


def decode(code):
    return tuple((code >> (2 * i)) & 3 for i in reversed(range(10)))


def encode(word):
    result = 0
    for direction in word:
        result = result * 4 + direction
    return result


def bond(a, b):
    return tuple(sorted((a, b)))


windows = {}
depth_counts = Counter()


def generate(word, code, vertices, used):
    depth_counts[len(word)] += 1
    if len(word) == 10:
        assert code not in windows
        windows[code] = (word, vertices, frozenset(used))
        return
    x, y = vertices[-1]
    for direction, (dx, dy) in enumerate(STEPS):
        next_vertex = (x + dx, y + dy)
        edge = bond(vertices[-1], next_vertex)
        if edge not in used:
            generate(word + (direction,), code * 4 + direction,
                     vertices + (next_vertex,), used | {edge})


generate((), 0, ((0, 0),), set())
assert [depth_counts[i] for i in range(1, 11)] == [4, 12, 36, 108, 316, 916, 2628, 7500, 21268, 60092]
print('GENERATED depth counts:', [depth_counts[i] for i in range(1, 11)])
coverage_errors = [code for code, cls in enumerate(raw)
                   if cls > 3741 or ((cls < 3741) != (code in windows))]
assert not coverage_errors, coverage_errors[:10]
print('COVERAGE all 1048576 codes: valid classes iff raw trails; every other code is sentinel 3741')

representatives = [lane('representatives', 20, cls) for cls in range(3741)]
assert all(code < N and code in windows and raw[code] == cls
           for cls, code in enumerate(representatives))
assert len(set(raw[code] for code in windows)) == 3741
print('REPRESENTATIVES all 3741: valid, distinct, project to own class; class map is surjective')

destinations = [[lane('destinations', 12, 4 * cls + direction) for direction in range(4)]
                for cls in range(3741)]
kinds = [[lane('edgeKinds', 2, 4 * cls + direction) for direction in range(4)]
         for cls in range(3741)]
assert all(0 <= destinations[cls][direction] <= 3741 and
           ((destinations[cls][direction] == 0) == (kinds[cls][direction] == 3))
           for cls in range(3741) for direction in range(4))


def row(record):
    word, vertices, used = record
    endpoint = vertices[-1]
    revisit = endpoint in vertices[:-1]
    result = []
    for direction, (dx, dy) in enumerate(STEPS):
        edge = bond(endpoint, (endpoint[0] + dx, endpoint[1] + dy))
        allowed = direction != (word[-1] + 2) % 4 and edge not in used
        kind = 2 if revisit else (0 if direction == word[-1] else 1)
        successor = encode(word[1:] + (direction,))
        result.append((allowed, kind, successor))
    return result


rep_rows = [row(windows[code]) for code in representatives]
row_errors = []
for code, record in windows.items():
    cls = raw[code]
    for direction, (allowed, kind, successor) in enumerate(row(record)):
        rep_allowed, rep_kind, _ = rep_rows[cls][direction]
        conditions = [allowed == (destinations[cls][direction] != 0),
                      allowed == rep_allowed, kind == rep_kind]
        if allowed:
            conditions.extend([successor in windows,
                               kinds[cls][direction] == kind,
                               destinations[cls][direction] - 1 == raw[successor]])
            if kind != 2:
                conditions.append(record[0][-1] == decode(representatives[cls])[-1])
        if not all(conditions):
            row_errors.append((code, cls, direction, conditions))
assert not row_errors, row_errors[:10]
print('ROWS all 240368 raw-word/direction pairs: admissibility, all-direction representative kind, admitted stored kind/successor and nonrevisit arrival agree')
edge_counts = Counter(kinds[cls][direction] for cls in range(3741) for direction in range(4)
                      if destinations[cls][direction])
assert edge_counts == {0: 2516, 1: 5032, 2: 1872}
print('EDGE COUNTS:', dict(sorted(edge_counts.items())))

for index in range(275, 280):
    name = f'rawClass_{index}'
    lo = offsets['rawClass'][name]
    hi = lo + 16384  # exclusive, including any leading zero bits
    first, last = lo // 12, (hi - 1) // 12
    valid = [code for code in range(first, last + 1) if code in windows]
    whole = [code for code in range(first, last + 1) if lo <= 12 * code and 12 * code + 12 <= hi]
    print(f'TARGET {name} line {line_numbers[name]}: bits [{lo},{hi}), touched codes [{first},{last}], '
          f'{len(whole)} whole lanes, {len(valid)} valid touched codes, '
          f'{len(set(raw[code] for code in valid))} classes, '
          f'low/high lane offsets {lo % 12}/{hi % 12}')
    print('  HEX SHA256:', hashlib.sha256(hex_text[name].encode()).hexdigest())
    for code in (first, last):
        print(f'  boundary code {code}, word {"".join("ENWS"[d] for d in decode(code))}, class {raw[code]}, raw={code in windows}')
    if valid:
        print('  valid examples:', [(code, ''.join('ENWS'[d] for d in decode(code)), raw[code], representatives[raw[code]]) for code in valid[:3]])
print('ALL CHECKS PASSED')
