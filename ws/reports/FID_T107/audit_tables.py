from pathlib import Path
import re, json, hashlib
from collections import Counter

SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
s = SOURCE.read_text()
literals = {name: int(h, 16) for name, h in re.findall(r'private noncomputable def (\w+) : ℕ := 0x([0-9a-f]+)', s)}

# Interpret the actual parenthesized Lean assembly, retaining each literal's bit offset.
def assembly(name):
    expr = re.search(r'^noncomputable def ' + name + r' : ℕ := (.*)$', s, re.M).group(1)
    tokens = re.findall(r'\w+|<<<|\+|\(|\)', expr)
    pos = 0
    def atom():
        nonlocal pos
        t = tokens[pos]; pos += 1
        if t == '(':
            result = add()
            assert tokens[pos] == ')'; pos += 1
            return result
        return literals[t], {t: 0}
    def shift():
        nonlocal pos
        value, offsets = atom()
        while pos < len(tokens) and tokens[pos] == '<<<':
            pos += 1
            bits = int(tokens[pos]); pos += 1
            value <<= bits
            offsets = {k: v + bits for k, v in offsets.items()}
        return value, offsets
    def add():
        nonlocal pos
        value, offsets = shift()
        while pos < len(tokens) and tokens[pos] == '+':
            pos += 1
            other, other_offsets = shift()
            assert not (offsets.keys() & other_offsets.keys())
            value += other
            offsets.update(other_offsets)
        return value, offsets
    result = add()
    assert pos == len(tokens)
    return result

def lanes(value, width, count):
    data = value.to_bytes((width * count + 7) // 8, 'little')
    result = []
    for i in range(count):
        bit = width * i
        first, offset = divmod(bit, 8)
        size = (offset + width + 7) // 8
        result.append((int.from_bytes(data[first:first+size], 'little') >> offset) & ((1 << width)-1))
    return result

raw_packed, raw_offsets = assembly('rawClass')
rep_packed, rep_offsets = assembly('representatives')
dest_packed, dest_offsets = assembly('destinations')
kind_packed, kind_offsets = assembly('edgeKinds')
raw = lanes(raw_packed, 12, 4**10)
representatives = lanes(rep_packed, 20, 3741)
destinations = lanes(dest_packed, 12, 4*3741)
kinds = lanes(kind_packed, 2, 4*3741)

# Check the full expression has exactly the intended non-overlapping concatenation.
for name, value, offsets, total_bits in [
    ('rawClass', raw_packed, raw_offsets, 12*4**10),
    ('representatives', rep_packed, rep_offsets, 20*3741),
    ('destinations', dest_packed, dest_offsets, 12*4*3741),
    ('edgeKinds', kind_packed, kind_offsets, 2*4*3741)]:
    ordered = sorted(offsets.items(), key=lambda kv: kv[1])
    for j, (literal, offset) in enumerate(ordered):
        end = ordered[j+1][1] if j+1 < len(ordered) else total_bits
        assert 0 <= literals[literal] < 2**(end-offset), (literal, offset, end)
    assert ordered[0][1] == 0
    print('PACKING', name, 'chunks', len(offsets), 'bits', value.bit_length(), 'capacity', total_bits)

steps = [(1,0), (0,1), (-1,0), (0,-1)]
def decode(code):
    return tuple((code >> (2*(9-i))) & 3 for i in range(10))
def geometry(word):
    vertices = [(0,0)]
    bonds = []
    for d in word:
        x,y = vertices[-1]; dx,dy = steps[d]
        new = (x+dx,y+dy)
        bonds.append(frozenset((vertices[-1],new)))
        vertices.append(new)
    return vertices, bonds

def row(code):
    word = decode(code)
    vertices, bonds = geometry(word)
    assert len(set(bonds)) == 10
    used = set(bonds)
    endpoint = vertices[-1]
    revisit = endpoint in vertices[:-1]
    results = []
    for d,(dx,dy) in enumerate(steps):
        new = (endpoint[0]+dx, endpoint[1]+dy)
        allowed = d != (word[-1]+2)%4 and frozenset((endpoint,new)) not in used
        kind = 2 if revisit else (0 if d == word[-1] else 1)
        successor = ((code % 4**9)*4+d)
        results.append((allowed,kind,successor))
    return results

# Paper recursion: each unused unoriented bond is eligible, with no virtual bond.
valid = set()
counts = [0]*11
used = set()
def visit(depth, position, code):
    counts[depth] += 1
    if depth == 10:
        valid.add(code)
        return
    for d,(dx,dy) in enumerate(steps):
        new = (position[0]+dx,position[1]+dy)
        bond = frozenset((position,new))
        if bond not in used:
            used.add(bond)
            visit(depth+1,new,code*4+d)
            used.remove(bond)
visit(0,(0,0),0)
assert counts[1:] == [4,12,36,108,316,916,2628,7500,21268,60092]
assert all(v <= 3741 and (v < 3741) == (c in valid) for c,v in enumerate(raw))
print('RAW_COUNTS',counts[1:])
print('RAW_COVERAGE', len(valid), 'valid;', len(raw)-len(valid), 'invalid; all lanes match')
assert all(c < 4**10 and c in valid and raw[c] == a for a,c in enumerate(representatives))
assert set(raw[c] for c in valid) == set(range(3741))
assert all(0 <= d <= 3741 and ((d == 0) == (k == 3)) for d,k in zip(destinations,kinds))
rep_rows = [row(c) for c in representatives]
checks = Counter()
for c in sorted(valid):
    a = raw[c]
    for d,(allowed,kind,successor) in enumerate(row(c)):
        stored_dest, stored_kind = destinations[4*a+d], kinds[4*a+d]
        assert allowed == (stored_dest != 0), ('allowed',c,a,d)
        assert kind == rep_rows[a][d][1], ('representative kind on every direction',c,a,d)
        checks['admissibility'] += 1
        checks['representative_kind_all_directions'] += 1
        # The supplied Lean correctness check tests kind on admitted edges.
        if allowed:
            assert kind == stored_kind, ('kind',c,a,d)
            assert successor in valid and raw[successor] == stored_dest-1, ('successor',c,a,d)
            checks['admitted_kind_successor'] += 1
            if kind != 2:
                assert c%4 == representatives[a]%4, ('arrival',c,a,d)
                checks['nonrevisit_arrival'] += 1
edge_counts = Counter(k for d,k in zip(destinations,kinds) if d != 0)
assert edge_counts == {0:2516, 1:5032, 2:1872}
print('REPRESENTATIVES_AND_ROWS', 'all 3741 representatives valid and map back; all raw rows compatible',dict(checks))
print('LABELLED_EDGE_COUNTS',dict(edge_counts))

summaries = {}
for k in range(500,505):
    name = f'rawClass_{k}'
    offset = raw_offsets[name]
    bits = 16384
    low, high = offset//12, (offset+bits-1)//12
    complete_low, complete_high = (offset+11)//12, (offset+bits)//12-1
    touched = list(range(low,high+1))
    valid_touched = [c for c in touched if c in valid]
    lane_stats = Counter(raw[c] for c in touched)
    summary = dict(source_line=next(i for i,l in enumerate(s.splitlines(),1) if l.startswith('private noncomputable def '+name+' ')),
        bit_interval=[offset,offset+bits-1], touched_codes=[low,high], complete_codes=[complete_low,complete_high],
        valid_touched=len(valid_touched), invalid_touched=len(touched)-len(valid_touched),
        distinct_valid_classes=len({raw[c] for c in valid_touched}),
        complete_valid=sum(c in valid for c in range(complete_low,complete_high+1)),
        sha256_hex=hashlib.sha256(format(literals[name],'04096x').encode()).hexdigest())
    summaries[name]=summary
    print('DECL',name,json.dumps(summary))
    if valid_touched:
        print('SAMPLES',[(c,''.join('ENWS'[d] for d in decode(c)),raw[c],representatives[raw[c]]) for c in valid_touched[:4]])
    else:
        prefix = decode(low)[:4]
        print('INVALID_RANGE_PREFIX_SAMPLE',''.join('ENWS'[d] for d in prefix), 'first word', ''.join('ENWS'[d] for d in decode(low)))
Path('audit_results.json').write_text(json.dumps(dict(counts=counts[1:],checks=dict(checks),edges=dict(edge_counts),declarations=summaries),indent=2)+'\n')
