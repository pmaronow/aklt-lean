"""Read-only, exact Python reconstruction of the assigned Lean literal data.
Only reads the supplied Lean source; creates no input files.
"""
from pathlib import Path
import ast
import collections
import hashlib
import json
import re

SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
text = SOURCE.read_text()
lines = text.splitlines()
values = {}
line_numbers = {}
expressions = {}
for lineno, line in enumerate(lines, 1):
    literal = re.fullmatch(r'private noncomputable def (\w+) : ℕ := (0x[0-9a-f]+)', line)
    if literal:
        name, token = literal.groups()
        assert name not in values
        values[name] = int(token, 16)
        line_numbers[name] = lineno
    combined = re.fullmatch(r'noncomputable def (rawClass|representatives|destinations|edgeKinds) : ℕ := (.+)', line)
    if combined:
        name, expr = combined.groups()
        expressions[name] = ast.parse(expr.replace('<<<', '<<'), mode='eval').body
        line_numbers[name] = lineno

# Accept only the grammar actually present, and retain each literal's bit offset.
def reconstruct(node, offset=0):
    if isinstance(node, ast.Name):
        assert node.id in values
        return values[node.id], {node.id: offset}
    assert isinstance(node, ast.BinOp)
    if isinstance(node.op, ast.Add):
        left, lo = reconstruct(node.left, offset)
        right, ro = reconstruct(node.right, offset)
        assert not lo.keys() & ro.keys()
        return left + right, lo | ro
    assert isinstance(node.op, ast.LShift)
    assert isinstance(node.right, ast.Constant) and isinstance(node.right.value, int)
    amount = node.right.value
    assert amount >= 0
    value, offsets = reconstruct(node.left, offset + amount)
    return value << amount, offsets

packed = {}
positions = {}
for name, expr in expressions.items():
    packed[name], positions[name] = reconstruct(expr)
    intervals = sorted((shift, shift + values[leaf].bit_length(), leaf)
                       for leaf, shift in positions[name].items())
    assert all(hi <= nxtlo for (_, hi, _), (nxtlo, _, _) in zip(intervals, intervals[1:])), name
    assert set(positions[name]) == {n for n in values if n.startswith(name + '_')}
print('Read whole source:', len(lines), 'lines;', len(text), 'characters;', len(values), 'literal declarations')
print('All four concatenations parsed exactly; every literal used once; no overlapping bits/carry.')

def lanes(name, width, count):
    number = packed[name]
    raw = number.to_bytes((number.bit_length() + 7) // 8, 'little') + b'\x00' * 3
    return [(int.from_bytes(raw[(width*i)//8:(width*i)//8 + 3], 'little') >> ((width*i)%8)) & ((1 << width)-1)
            for i in range(count)]

N = 4**10
raw_class = lanes('rawClass', 12, N)
rep = lanes('representatives', 20, 3741)
dest = lanes('destinations', 12, 3741*4)
kind = lanes('edgeKinds', 2, 3741*4)
assert all(c <= 3741 for c in raw_class)
assert all(c < N for c in rep)
assert all(c <= 3741 for c in dest)
assert all((v == 0) == (k == 3) for v, k in zip(dest, kind))

# Independent lattice trail enumeration from d:memory-automaton.
steps = ((1,0), (0,1), (-1,0), (0,-1))
def bond(p, q):
    return (p,q) if p < q else (q,p)
def geometry(code):
    word = tuple((code >> (2*i)) & 3 for i in range(9,-1,-1))
    p = (0,0)
    used = set()
    departures = set()
    valid = True
    for d in word:
        departures.add(p)
        dx,dy = steps[d]
        q = (p[0]+dx,p[1]+dy)
        edge = bond(p,q)
        valid &= edge not in used
        used.add(edge)
        p = q
    return word, p, used, departures, valid

counts = [0]*11
raw_codes = set()
raw_details = {}
def generate(depth, code, p, used, departures, word):
    counts[depth] += 1
    if depth == 10:
        raw_codes.add(code)
        raw_details[code] = (word, p, frozenset(used), frozenset(departures))
        return
    for d,(dx,dy) in enumerate(steps):
        q = (p[0]+dx,p[1]+dy)
        edge = bond(p,q)
        if edge not in used:
            generate(depth+1, code*4+d, q, used | {edge}, departures | {p}, word+(d,))
generate(0,0,(0,0),set(),set(),())
assert counts[1:] == [4,12,36,108,316,916,2628,7500,21268,60092]
assert all((c < 3741) == (code in raw_codes) for code,c in enumerate(raw_class))
print('Regenerated counts:', counts[1:])
print('Exact coverage checked on all', N, 'codes: raw class 0..3740 iff a raw window; 3741 otherwise.')

for a, code in enumerate(rep):
    assert code in raw_codes and raw_class[code] == a

edge_counts = collections.Counter()
# Check against stored rows and representatives on ALL raw windows, including
# the paper's kind comparison on inadmissible directions.
for code,(word,p,used,departures) in raw_details.items():
    a = raw_class[code]
    rword,rp,rused,rdepartures = raw_details[rep[a]]
    revisit = p in departures
    rrevisit = rp in rdepartures
    for d,(dx,dy) in enumerate(steps):
        q = (p[0]+dx,p[1]+dy)
        rq = (rp[0]+dx,rp[1]+dy)
        allowed = d != (word[-1]+2)%4 and bond(p,q) not in used
        rallowed = d != (rword[-1]+2)%4 and bond(rp,rq) not in rused
        k = 2 if revisit else (0 if d == word[-1] else 1)
        rk = 2 if rrevisit else (0 if d == rword[-1] else 1)
        i = a*4+d
        assert allowed == rallowed == (dest[i] != 0), (code,a,d,'allowed')
        assert k == rk, (code,a,d,'representative kind')
        if allowed:
            assert kind[i] == k, (code,a,d,'stored kind')
            successor = (code % 4**9)*4+d
            assert successor in raw_codes
            assert dest[i]-1 == raw_class[successor], (code,a,d,'successor')
            if k != 2:
                assert word[-1] == rword[-1], (code,a,d,'arrival')
for v,k in zip(dest,kind):
    if v: edge_counts[k] += 1
assert dict(edge_counts) == {0:2516,1:5032,2:1872}
print('All representatives, labelled rows, kinds, successors and nonrevisit arrivals checked on 60092 raw words.')
print('Quotient edge counts:',dict(sorted(edge_counts.items())))

assigned = []
for n in range(680,685):
    name = f'rawClass_{n}'
    lo = positions['rawClass'][name]
    hi = lo + 16384 - 1
    codes = range(lo//12, hi//12 + 1)
    valid = [c for c in codes if c in raw_codes]
    entry = dict(name=name, line=line_numbers[name], bits=values[name].bit_length(),
                 offset=lo, last_bit=hi, first_code=codes.start, last_code=codes.stop-1,
                 affected_codes=len(codes), raw_windows=len(valid), invalid_codes=len(codes)-len(valid),
                 first_valid=valid[:3], last_valid=valid[-3:],
                 value_sha256=hashlib.sha256(values[name].to_bytes(2048,'big')).hexdigest())
    assigned.append(entry)
    print(json.dumps(entry,sort_keys=True))
    for c in valid[:2] + valid[-2:]:
        word,_,_,_ = raw_details[c]
        print('  example',c,''.join('ENWS'[d] for d in word),'class',raw_class[c],'rep_code',rep[raw_class[c]])

# Show the exact boundary entries, so partial 12-bit lanes are not ignored.
for n in range(680,685):
    name=f'rawClass_{n}'
    lo=positions['rawClass'][name]
    hi=lo+16384-1
    print('boundary',name,[(c, raw_class[c], c in raw_codes) for c in sorted({lo//12,hi//12})])
Path('/home/ubuntu/aklt/reports/FID_T143/check_results.json').write_text(json.dumps({'counts':counts[1:],'edge_counts':dict(edge_counts),'assigned':assigned},indent=2)+'\n')
print('PASS: every asserted finite check completed.')
