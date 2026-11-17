"""Read-only reconstruction check for the literal automaton data.

Run with python3 check_data.py. No Lean processes or external witness files used.
"""
import ast
from collections import Counter
from pathlib import Path
import re

SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
text = SOURCE.read_text()
definitions = {}
line_numbers = {}
for line_no, line in enumerate(text.splitlines(), 1):
    match = re.fullmatch(r'(?:private )?noncomputable def (\w+) : ℕ := (.+)', line)
    if match:
        name, body = match.groups()
        definitions[name] = body
        line_numbers[name] = line_no


def parse(name):
    # All shifts in this file have a parenthesized application and a literal
    # shift amount; reject any ambiguous Python/Lean precedence interpretation.
    body = definitions[name]
    for match in re.finditer(r'<<< (\d+)', body):
        assert body[match.end()] == ')'
    return ast.parse(body.replace('<<<', '<<'), mode='eval').body


def fragments(node, offset=0):
    if isinstance(node, ast.Name):
        return [(node.id, offset)]
    assert isinstance(node, ast.BinOp)
    if isinstance(node.op, ast.Add):
        return fragments(node.left, offset) + fragments(node.right, offset)
    assert isinstance(node.op, ast.LShift)
    assert isinstance(node.right, ast.Constant) and type(node.right.value) is int
    return fragments(node.left, offset + node.right.value)


def unpack(name, width, count):
    parts = fragments(parse(name))
    assert len({part for part, _ in parts}) == len(parts)
    packed = 0
    intervals = []
    for part, offset in parts:
        body = definitions[part]
        assert re.fullmatch(r'0x[0-9a-f]+', body)
        # The literal's written hex width is its allocated fragment width.
        bits = 4 * (len(body) - 2)
        value = int(body, 16)
        assert value < 2**bits
        intervals.append((offset, offset + bits, part))
        packed += value << offset
    intervals.sort()
    assert intervals[0][0] == 0
    assert all(a[1] == b[0] for a, b in zip(intervals, intervals[1:]))
    assert intervals[-1][1] <= width * count
    assert packed < 2**(width * count)
    if width % 4 == 0:
        digits = width // 4
        hx = format(packed, f'0{count * digits}x')
        lanes = [int(hx[i:i + digits], 16) for i in range(0, len(hx), digits)][::-1]
    else:
        assert width == 2
        hx = format(packed, f'0{(count + 1) // 2}x')
        lanes = []
        for digit in reversed(hx):
            value = int(digit, 16)
            lanes.extend((value & 3, value >> 2))
        lanes = lanes[:count]
    assert len(lanes) == count
    print(f'{name}: {len(parts)} nonoverlapping contiguous fragments, '
          f'{intervals[-1][1]} written bits, {packed.bit_length()} significant bits, '
          f'{count} lanes of width {width}')
    return lanes, {part: (lo, hi) for lo, hi, part in intervals}


raw, raw_intervals = unpack('rawClass', 12, 4**10)
representatives, _ = unpack('representatives', 20, 3741)
destinations, _ = unpack('destinations', 12, 3741 * 4)
kinds, _ = unpack('edgeKinds', 2, 3741 * 4)
assert len(definitions) == 768 + 5 + 11 + 2 + 4
assert all(0 <= x <= 3741 for x in raw)
assert all(x < 4**10 for x in representatives)
assert all(0 <= x <= 3741 for x in destinations)
assert all((dst == 0) == (kind == 3) for dst, kind in zip(destinations, kinds))
print('All raw values, representatives, successor offsets, and kind sentinels are in range.')

STEPS = [(1, 0), (0, 1), (-1, 0), (0, -1)]


def bond(x, y):
    return tuple(sorted((x, y)))


def geometry(code):
    # Most-significant-first, with E,N,W,S = 0,1,2,3.
    word = tuple((code >> (2 * i)) & 3 for i in reversed(range(10)))
    vertex = (0, 0)
    vertices = [vertex]
    bonds = []
    for d in word:
        dx, dy = STEPS[d]
        nxt = (vertex[0] + dx, vertex[1] + dy)
        bonds.append(bond(vertex, nxt))
        vertices.append(nxt)
        vertex = nxt
    return word, vertices, bonds


counts = [0] * 11
generated = set()


def generate(depth, code, x, y, used):
    counts[depth] += 1
    if depth == 10:
        generated.add(code)
        return
    for d, (dx, dy) in enumerate(STEPS):
        nxt = (x + dx, y + dy)
        edge = bond((x, y), nxt)
        if edge in used:
            continue
        used.add(edge)
        generate(depth + 1, 4 * code + d, *nxt, used)
        used.remove(edge)


generate(0, 0, 0, 0, set())
assert counts == [1, 4, 12, 36, 108, 316, 916, 2628, 7500, 21268, 60092]
assert generated == {code for code, cls in enumerate(raw) if cls < 3741}
assert set(raw[code] for code in generated) == set(range(3741))
print('Independent used-bond recursion counts:', counts)
print('All 1048576 raw/sentinel lanes agree with independent trail generation; all 3741 classes occur.')

for cls, rep in enumerate(representatives):
    assert rep in generated and raw[rep] == cls, (cls, rep)
print('All 3741 supplied representatives are raw and map to their stated class.')

admitted = Counter()
for code in sorted(generated):
    word, vertices, used_list = geometry(code)
    assert len(set(used_list)) == 10
    cls = raw[code]
    x, y = vertices[-1]
    used = set(used_list)
    revisit = vertices[-1] in vertices[:-1]
    rep_word, rep_vertices, _ = geometry(representatives[cls])
    rep_revisit = rep_vertices[-1] in rep_vertices[:-1]
    for d, (dx, dy) in enumerate(STEPS):
        slot = 4 * cls + d
        allowed = d != (word[-1] + 2) % 4 and bond((x, y), (x + dx, y + dy)) not in used
        assert allowed == (destinations[slot] != 0), ('allowed', code, cls, d)
        kind = 2 if revisit else 0 if d == word[-1] else 1
        # The paper's kind equality is also checked on forbidden directions.
        rep_kind = 2 if rep_revisit else 0 if d == rep_word[-1] else 1
        assert kind == rep_kind, ('representative kind', code, cls, d)
        if allowed:
            assert kinds[slot] == kind, ('kind', code, cls, d)
            successor = (code % 4**9) * 4 + d
            assert successor in generated
            assert destinations[slot] - 1 == raw[successor], ('successor', code, cls, d)
            if kind != 2:
                assert word[-1] == rep_word[-1], ('arrival', code, cls, d)
            admitted[kind] += 1
edge_counts = Counter(kind for dst, kind in zip(destinations, kinds) if dst != 0)
assert edge_counts == {0: 2516, 1: 5032, 2: 1872}
print('All 60092 raw words x 4 directions satisfy admissibility, kind, successor, and arrival checks.')
print('Admitted raw edges by kind:', dict(sorted(admitted.items())))
print('Labelled quotient edges by kind:', dict(sorted(edge_counts.items())))

for n in range(580, 585):
    name = f'rawClass_{n}'
    lo, hi = raw_intervals[name]
    first, last = lo // 12, (hi - 1) // 12
    raw_codes = sorted(generated.intersection(range(first, last + 1)))
    values = [raw[code] for code in raw_codes]
    print(f'{name} at source line {line_numbers[name]}: bit interval [{lo},{hi}); '
          f'affects code interval [{first},{last}]; '
          f'{len(raw_codes)} raw words and {last - first + 1 - len(raw_codes)} invalid codes; '
          f'{len(set(values))} distinct classes; '
          f'raw class range {min(values) if values else None}..{max(values) if values else None}; '
          f'boundary residues {lo % 12},{hi % 12}')
    if raw_codes:
        print(f'  first/last raw (code,class): {(raw_codes[0], raw[raw_codes[0]])}, '
              f'{(raw_codes[-1], raw[raw_codes[-1]])}')
print('PASS: all finite reconstruction checks above.')
