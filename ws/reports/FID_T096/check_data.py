"""Read-only reconstruction of the designated Lean literals and paper trail checks."""
from pathlib import Path
from collections import Counter
import hashlib
import json
import re

SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
OUT = Path('/home/ubuntu/aklt/reports/FID_T096')
text = SOURCE.read_text()
values = {}
layouts = {}
lines = {}
hex_widths = {}

# All nontrivial expressions in these four tables are fully parenthesized.
# Track every literal's offset as well as its exact unbounded natural value.
def parse_expression(expression):
    tokens = re.findall(r'\w+|<<<|[()+]', expression)
    assert ''.join(tokens) == re.sub(r'\s+', '', expression)
    pos = 0
    def atom():
        nonlocal pos
        token = tokens[pos]
        pos += 1
        if token == '(':
            result = expr()
            assert tokens[pos] == ')'
            pos += 1
            return result
        if token.isdecimal():
            return int(token), []
        return values[token], [(token, 0)]
    def expr():
        nonlocal pos
        value, layout = atom()
        if pos < len(tokens) and tokens[pos] in ('+', '<<<'):
            op = tokens[pos]
            pos += 1
            right, right_layout = atom()
            if op == '+':
                value += right
                layout += right_layout
            else:
                assert not right_layout
                value <<= right
                layout = [(name, offset + right) for name, offset in layout]
            assert pos == len(tokens) or tokens[pos] == ')', 'unexpected unparenthesized chain'
        return value, layout
    result = expr()
    assert pos == len(tokens)
    return result

for line_no, line in enumerate(text.splitlines(), 1):
    match = re.fullmatch(r'(?:private )?noncomputable def (\w+) : ℕ := (.+)', line)
    if not match:
        continue
    name, expression = match.groups()
    lines[name] = line_no
    if expression.startswith('0x'):
        assert re.fullmatch(r'0x[0-9a-f]+', expression)
        values[name] = int(expression, 16)
        hex_widths[name] = len(expression) - 2
    else:
        values[name], layouts[name] = parse_expression(expression)

# Check the concatenation has no gaps/overlaps, including its short final fragment.
for name in ('rawClass', 'representatives', 'destinations', 'edgeKinds'):
    ordered = sorted(layouts[name], key=lambda item: item[1])
    next_offset = 0
    for leaf, offset in ordered:
        assert offset == next_offset
        width = 4 * hex_widths[leaf]
        assert values[leaf] < 2**width
        next_offset += width
    print(name, 'literal_count', len(ordered), 'allocated_bits', next_offset,
          'value_bits', values[name].bit_length())

# Decode via fixed-width hexadecimal digits. This is exactly floor(N/2^(w*i)) mod 2^w.
def lanes(name, width, count):
    assert width % 4 == 0
    digits = width // 4
    encoded = format(values[name], 'x').zfill(digits * count)
    assert len(encoded) == digits * count
    return [int(encoded[len(encoded)-(i+1)*digits:len(encoded)-i*digits], 16)
            for i in range(count)]

N = 4**10
Q = 3741
classes = lanes('rawClass', 12, N)
representatives = lanes('representatives', 20, Q)
destinations = lanes('destinations', 12, Q*4)
# The 2-bit kind lanes straddle hexadecimal digits, so decode the bytes once.
kind_bytes = values['edgeKinds'].to_bytes((Q*4*2 + 7)//8, 'little')
kinds = [(kind_bytes[i//4] >> (2*(i%4))) & 3 for i in range(Q*4)]
assert max(classes) <= Q
assert max(representatives) < N
assert max(destinations) <= Q
assert all((dst == 0) == (kind == 3) for dst, kind in zip(destinations, kinds))
assert all(dst == 0 or kind < 3 for dst, kind in zip(destinations, kinds))

STEPS = ((1,0), (0,1), (-1,0), (0,-1))

def bond(a, b):
    return (a,b) if a < b else (b,a)

def decode(code):
    return [(code >> (2*(9-i))) & 3 for i in range(10)]

def geometry(word):
    vertices = [(0,0)]
    bonds = set()
    for direction in word:
        dx,dy = STEPS[direction]
        x,y = vertices[-1]
        endpoint = (x+dx,y+dy)
        edge = bond(vertices[-1], endpoint)
        assert edge not in bonds
        bonds.add(edge)
        vertices.append(endpoint)
    return vertices, bonds

# Generate the independent raw domain exactly as specified in app-input-contracts.tex:232-237.
raw = {}
level_counts = Counter()
def generate(word, code, vertices, bonds):
    level_counts[len(word)] += 1
    if len(word) == 10:
        raw[code] = (tuple(word), tuple(vertices), frozenset(bonds))
        return
    x,y = vertices[-1]
    for direction,(dx,dy) in enumerate(STEPS):
        endpoint = (x+dx,y+dy)
        edge = bond(vertices[-1],endpoint)
        if edge not in bonds:
            generate(word+[direction],code*4+direction,vertices+[endpoint],bonds|{edge})
generate([],0,[(0,0)],set())
assert [level_counts[j] for j in range(1,11)] == [4,12,36,108,316,916,2628,7500,21268,60092]
assert len(raw) == 60092
assert set(code for code, a in enumerate(classes) if a < Q) == set(raw)
assert set(classes[code] for code in raw) == set(range(Q))
assert all(code in raw and classes[code] == a for a,code in enumerate(representatives))
print('Raw counts:', dict(sorted(level_counts.items())))
print('Domain coverage: all 1048576 words checked; 60092 valid; 988484 invalid.')

# Regenerate each raw window's four labelled departures, then compare with its class row.
# Full global check makes any local defect, or incorrect referenced target class, visible.
errors = []
edge_counts = Counter()
for a in range(Q):
    for d in range(4):
        if destinations[4*a+d] != 0:
            edge_counts[kinds[4*a+d]] += 1
checked_edges = 0
for code,(word,vertices,bonds) in raw.items():
    a = classes[code]
    last = word[-1]
    endpoint = vertices[-1]
    revisit = endpoint in vertices[:-1]
    for d,(dx,dy) in enumerate(STEPS):
        allowed = d != (last+2)%4 and bond(endpoint,(endpoint[0]+dx,endpoint[1]+dy)) not in bonds
        ix = 4*a+d
        # The paper lemma also compares raw kinds on inadmissible directions.
        rep_word, rep_vertices, _ = raw[representatives[a]]
        rep_revisit = rep_vertices[-1] in rep_vertices[:-1]
        raw_kind = 2 if revisit else (0 if d == last else 1)
        representative_kind = 2 if rep_revisit else (0 if d == rep_word[-1] else 1)
        if raw_kind != representative_kind:
            errors.append((code,a,d,'raw/representative unconditional kind'))
        if (destinations[ix] != 0) != allowed:
            errors.append((code,a,d,'admissibility'))
        if not allowed:
            continue
        checked_edges += 1
        kind = 2 if revisit else (0 if d == last else 1)
        successor = (code % (4**9))*4+d
        if kinds[ix] != kind:
            errors.append((code,a,d,'kind'))
        if destinations[ix]-1 != classes[successor]:
            errors.append((code,a,d,'successor'))
        if kind != 2 and representatives[a]%4 != last:
            errors.append((code,a,d,'arrival'))
assert edge_counts == {0:2516,1:5032,2:1872}, edge_counts
assert not errors, errors[:20]
print('Global quotient checks (including unconditional raw/representative kinds):', len(raw)*4, 'direction tests;', checked_edges,
      'admissible raw edges; quotient edge counts', dict(sorted(edge_counts.items())), '; no mismatches.')

# Reconstruct the archived text format specified by the paper from the decoded data.
archive_rows = [[60092, Q]]
archive_rows += [[code, classes[code]] for code in sorted(raw)]
archive_rows += [[representatives[a]] + [destinations[4*a+d]-1 for d in range(4)] +
                 [kinds[4*a+d] if kinds[4*a+d] < 3 else -1 for d in range(4)]
                 for a in range(Q)]
archive_text = ''.join(' '.join(map(str, row))+'\n' for row in archive_rows)
archive_hash = hashlib.sha256(archive_text.encode()).hexdigest()
expected_archive_hash = re.search(r'Archive SHA-256: ([0-9a-f]{64})', text)[1]
assert archive_hash == expected_archive_hash
print('Reconstructed archive:', len(archive_rows), 'lines;', len(archive_text.encode()),
      'bytes; SHA-256', archive_hash, '(matches the designated archive hash).')

# The literal is an internal encoding, not an independently labelled paper statement.
# Validate each target's exact span, including partial 12-bit lanes at either boundary.
summary = []
for j in range(445,450):
    name = f'rawClass_{j}'
    offset = dict(layouts['rawClass'])[name]
    width = 4*hex_widths[name]
    lo = offset//12
    hi = (offset+width-1)//12
    valid = [code for code in range(lo,hi+1) if code in raw]
    data = {
        'declaration': name,
        'line': lines[name],
        'bits_low': offset,
        'bits_high': offset+width-1,
        'lowest_code': lo,
        'highest_code': hi,
        'intersected_lanes': hi-lo+1,
        'valid_lanes': len(valid),
        'invalid_lanes': hi-lo+1-len(valid),
        'distinct_classes': len(set(classes[code] for code in valid)),
        'low_lane_bits_from_this_fragment': 12-offset%12,
        'high_lane_bits_from_this_fragment': (offset+width-1)%12+1,
        'sha256_hex_literal': hashlib.sha256(format(values[name],f'0{hex_widths[name]}x').encode()).hexdigest(),
    }
    if valid:
        code = valid[0]
        data['example'] = {'code':code, 'word':''.join('ENWS'[d] for d in decode(code)),
                           'class':classes[code], 'representative_code':representatives[classes[code]]}
    summary.append(data)
    print(json.dumps(data,sort_keys=True))
(OUT/'check_results.json').write_text(json.dumps({'raw_counts':dict(level_counts),
    'raw_window_count':len(raw),'checked_raw_direction_tests':len(raw)*4,
    'checked_admissible_raw_edges':checked_edges,'quotient_edge_counts':dict(edge_counts),
    'mismatches':errors,'reconstructed_archive_sha256':archive_hash,
    'reconstructed_archive_lines':len(archive_rows),'reconstructed_archive_bytes':len(archive_text.encode()),
    'declarations':summary},indent=2)+'\n')
