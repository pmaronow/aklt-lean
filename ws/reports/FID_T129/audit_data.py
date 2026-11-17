"""Read-only reconstruction checks for the assigned Automaton10Data slices."""
from pathlib import Path
import ast
from collections import Counter
import hashlib
import json
import re

SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
text = SOURCE.read_text()
literals = {}
locations = {}
hex_lengths = {}
for lineno, line in enumerate(text.splitlines(), 1):
    match = re.fullmatch(r'private noncomputable def (\w+) : ℕ := 0x([0-9a-f]+)', line)
    if match:
        name, digits = match.groups()
        literals[name] = int(digits, 16)
        locations[name] = lineno
        hex_lengths[name] = len(digits)

def expression(name):
    match = re.search(r'^noncomputable def ' + name + r' : ℕ := (.*)$', text, re.M)
    assert match
    return ast.parse(match[1].replace('<<<', '<<'), mode='eval').body

def terms(node, offset=0):
    if isinstance(node, ast.Name):
        return [(node.id, offset)]
    assert isinstance(node, ast.BinOp)
    if isinstance(node.op, ast.Add):
        return terms(node.left, offset) + terms(node.right, offset)
    assert isinstance(node.op, ast.LShift)
    assert isinstance(node.right, ast.Constant) and isinstance(node.right.value, int)
    return terms(node.left, offset + node.right.value)

def packed(name):
    ts = terms(expression(name))
    assert len(ts) == len(set(n for n, _ in ts))
    value = sum(literals[n] << off for n, off in ts)
    ordered = sorted(ts, key=lambda x: x[1])
    # No overlaps/carries between constituent literals.
    for (n, off), (_, next_off) in zip(ordered, ordered[1:]):
        assert literals[n].bit_length() <= next_off - off
    return value, dict(ts)

raw, offsets = packed('rawClass')
reps, _ = packed('representatives')
dests, _ = packed('destinations')
kinds, _ = packed('edgeKinds')
assert set(literals) == set(offsets) | {n for table in ['representatives', 'destinations', 'edgeKinds'] for n, _ in terms(expression(table))}
assert len(offsets) == 768
assert raw.bit_length() <= 12 * 4**10
raw_bytes = raw.to_bytes(12 * 4**10 // 8, 'little')

def raw_at(code):
    p = (code // 2) * 3
    triple = int.from_bytes(raw_bytes[p:p+3], 'little')
    return (triple >> (12 * (code % 2))) & 4095

def lane(value, width, index):
    return (value >> (width * index)) & ((1 << width) - 1)

STEPS = [(1, 0), (0, 1), (-1, 0), (0, -1)]
def decode(code):
    return tuple((code >> (2 * (9-i))) & 3 for i in range(10))

def geometry(word):
    vertex = (0, 0)
    vertices = [vertex]
    bonds = []
    for direction in word:
        dx, dy = STEPS[direction]
        nxt = (vertex[0]+dx, vertex[1]+dy)
        bonds.append(frozenset((vertex, nxt)))
        vertices.append(nxt)
        vertex = nxt
    return vertices, bonds

def row(word):
    vertices, bonds = geometry(word)
    endpoint = vertices[-1]
    revisit = endpoint in vertices[:-1]
    output = []
    for d, (dx, dy) in enumerate(STEPS):
        nxt = (endpoint[0]+dx, endpoint[1]+dy)
        allowed = d != (word[-1]+2) % 4 and frozenset((endpoint, nxt)) not in bonds
        kind = 2 if revisit else (0 if d == word[-1] else 1)
        output.append((allowed, kind))
    return output

raw_words = {}
counts = Counter()
def generate(word=(), code=0, vertex=(0, 0), bonds=frozenset()):
    if word:
        counts[len(word)] += 1
    if len(word) == 10:
        raw_words[code] = word
        return
    for d, (dx, dy) in enumerate(STEPS):
        nxt = (vertex[0]+dx, vertex[1]+dy)
        bond = frozenset((vertex, nxt))
        if bond not in bonds:
            generate(word+(d,), 4*code+d, nxt, bonds | {bond})
generate()
assert [counts[i] for i in range(1, 11)] == [4,12,36,108,316,916,2628,7500,21268,60092]

coverage_errors = []
for code in range(4**10):
    value = raw_at(code)
    if not (value <= 3741 and ((value < 3741) == (code in raw_words))):
        coverage_errors.append((code, value, code in raw_words))

representatives = []
rep_errors = []
for a in range(3741):
    code = lane(reps, 20, a)
    representatives.append(decode(code))
    if not (code < 4**10 and code in raw_words and raw_at(code) == a):
        rep_errors.append((a, code, raw_at(code)))

quotient_rows = []
edge_counts = Counter()
row_errors = []
for a, rep in enumerate(representatives):
    out = []
    for d, (allow, kind) in enumerate(row(rep)):
        destination = lane(dests, 12, a*4+d)
        stored_kind = lane(kinds, 2, a*4+d)
        successor = raw_at(((lane(reps,20,a) % 4**9)*4)+d)
        if not (destination <= 3741 and (destination == 0) == (stored_kind == 3)):
            row_errors.append(('stored bound/sentinel', a,d,destination,stored_kind))
        if allow:
            edge_counts[kind] += 1
            if destination != successor+1 or stored_kind != kind:
                row_errors.append(('representative transition',a,d,destination,stored_kind,successor,kind))
        elif destination != 0:
            row_errors.append(('inadmissible representative',a,d,destination))
        out.append((destination,stored_kind))
    quotient_rows.append(out)

raw_transition_errors = []
for code, word in raw_words.items():
    a = raw_at(code)
    if a >= 3741:
        continue
    rep_row = row(representatives[a])
    for d, (allow, kind) in enumerate(row(word)):
        destination, stored_kind = quotient_rows[a][d]
        # The quotient lemma compares mathematical kinds for all directions,
        # even where the archive stores the inadmissible-edge marker -1.
        if rep_row[d] != (allow,kind):
            raw_transition_errors.append(('raw/representative admissibility or kind',code,a,d))
        if (destination != 0) != allow:
            raw_transition_errors.append(('admissibility',code,a,d))
        if allow:
            next_class = raw_at((code % 4**9)*4+d)
            if destination != next_class+1 or stored_kind != kind:
                raw_transition_errors.append(('kind/successor',code,a,d,next_class,destination,kind,stored_kind))
            if kind != 2 and representatives[a][-1] != word[-1]:
                raw_transition_errors.append(('arrival',code,a,d))

print('Parsed all literal data and all four assembly expressions.')
print('Literal groups:', dict(Counter(re.sub(r'_\d+$','',n) for n in literals)))
print('Raw counts:', dict(sorted(counts.items())))
print('Coverage errors:', len(coverage_errors), coverage_errors[:5])
print('Representative errors:', len(rep_errors), rep_errors[:5])
print('Quotient row errors:', len(row_errors), row_errors[:5])
print('Raw transition errors:', len(raw_transition_errors), raw_transition_errors[:5])
print('Edge counts (0=straight,1=turn,2=revisit):', dict(edge_counts))

# Reconstruct the natural whitespace-separated text layout described by the
# paper, then check it against the archive digest recorded in the Lean file.
archive_rows = [[60092,3741]]
archive_rows += [[code,raw_at(code)] for code in sorted(raw_words)]
for a in range(3741):
    archive_rows.append([lane(reps,20,a)] +
        [lane(dests,12,a*4+d)-1 for d in range(4)] +
        [k if (k := lane(kinds,2,a*4+d)) != 3 else -1 for d in range(4)])
archive = ''.join(' '.join(map(str,r))+'\n' for r in archive_rows).encode()
archive_sha = hashlib.sha256(archive).hexdigest()
declared_sha = re.search(r'Archive SHA-256: ([0-9a-f]{64})',text)[1]
print('Reconstructed archive SHA-256:', archive_sha)
print('Matches file provenance SHA-256:', archive_sha == declared_sha)

slice_results = []
for i in range(610,615):
    name = f'rawClass_{i}'
    value = literals[name]
    off = offsets[name]
    assert hex_lengths[name] == 4096
    bit_end = off + 16384
    first, last = off//12, (bit_end-1)//12
    covered = list(range(first,last+1))
    valid = [c for c in covered if c in raw_words]
    invalid = [c for c in covered if c not in raw_words]
    # Reconstruct exactly the whole assigned literal, including partial lanes at boundaries.
    expected = 0
    for code in covered:
        cls = raw_at(code) if code in raw_words else 3741
        lane_start = 12*code
        start = max(off,lane_start)
        end = min(bit_end,lane_start+12)
        fragment = (cls >> (start-lane_start)) & ((1 << (end-start))-1)
        expected |= fragment << (start-off)
    assert expected == value
    prefix = ''
    for ds in zip(*(decode(c) for c in covered)):
        if len(set(ds)) != 1:
            break
        prefix += 'ENWS'[ds[0]]
    result = dict(name=name,line=locations[name],hex_digits=hex_lengths[name],
                  bit_start=off,bit_end_exclusive=bit_end,
                  first_code=first,last_code=last,
                  first_word=''.join('ENWS'[d] for d in decode(first)),
                  last_word=''.join('ENWS'[d] for d in decode(last)),
                  first_lane_bit=off%12,last_lane_bit_end=(bit_end-1)%12+1,
                  raw_words=len(valid),nonraw_words=len(invalid),
                  raw_classes=sorted({raw_at(c) for c in valid}),
                  first_raw_examples=[(c,raw_at(c)) for c in valid[:3]],
                  common_prefix=prefix,exact_reconstruction=True,
                  sha256_hex=hashlib.sha256(format(value,'x').encode()).hexdigest())
    slice_results.append(result)
    print(json.dumps({k:v for k,v in result.items() if k != 'raw_classes'}))

Path('audit_results.json').write_text(json.dumps(dict(
    counts=dict(counts),coverage_errors=coverage_errors,
    representative_errors=rep_errors,quotient_row_errors=row_errors,
    raw_transition_errors=raw_transition_errors,edge_counts=dict(edge_counts),
    slices=slice_results,archive_sha256=archive_sha,
    archive_provenance_matches=(archive_sha == declared_sha)),indent=2)+'\n')
