"""Read only the supplied Lean data; independently check the paper's finite contract."""
from pathlib import Path
import ast
import collections
import hashlib
import json
import re

ROOT = Path('/home/ubuntu/aklt/review/FID_T/lean')
source = (ROOT / 'AKLT/Defs/Automaton10Data.lean').read_text()
values = {}
exprs = {}
lines = {}
for lineno, line in enumerate(source.splitlines(), 1):
    match = re.fullmatch(r'(?:private )?noncomputable def (\w+) : ℕ := (.+)', line)
    if match:
        name, expr = match.groups()
        values[name] = eval(expr.replace('<<<', '<<'), {'__builtins__': {}}, values)
        exprs[name] = expr
        lines[name] = lineno

# Independently identify each leaf's bit offset in the exact assembly expression.
def leaves(node, offset=0):
    if isinstance(node, ast.Name):
        return [(node.id, offset)]
    assert isinstance(node, ast.BinOp)
    if isinstance(node.op, ast.LShift):
        assert isinstance(node.right, ast.Constant)
        return leaves(node.left, offset + node.right.value)
    assert isinstance(node.op, ast.Add)
    return leaves(node.left, offset) + leaves(node.right, offset)
raw_leaves = leaves(ast.parse(exprs['rawClass'].replace('<<<', '<<'), mode='eval').body)
assert [x[0] for x in raw_leaves] == [f'rawClass_{i}' for i in range(768)]
assert all(values[n] < 2 ** (off_prev-off) for (_,off_prev),(n,off) in zip(raw_leaves,raw_leaves[1:]))
assert values[raw_leaves[0][0]] < 2 ** (12 * 4**10 - raw_leaves[0][1])
# Convert whole integers to bytes once: no rounding of numbers or lane boundaries.
def lanes(name, width, count):
    val = values[name]
    assert val < 1 << (width * count)
    packed = val.to_bytes((width * count+7)//8, 'little')
    result = []
    for i in range(count):
        bit = width*i
        byte, shift = divmod(bit,8)
        result.append((int.from_bytes(packed[byte:byte+4], 'little') >> shift) & ((1<<width)-1))
    return result
classes = lanes('rawClass', 12, 4**10)
reps = lanes('representatives', 20, 3741)
dests = lanes('destinations', 12, 4*3741)
kinds = lanes('edgeKinds', 2, 4*3741)
assert all(0 <= a <= 3741 for a in classes)
assert all(code < 4**10 for code in reps)
assert all(0 <= a <= 3741 for a in dests)
assert all((a == 0) == (k == 3) for a,k in zip(dests,kinds))
steps = ((1,0),(0,1),(-1,0),(0,-1))

def decode(code):
    return tuple((code >> (2*j)) & 3 for j in range(9,-1,-1))

def encode(word):
    code=0
    for d in word:
        code=4*code+d
    return code

def geometry(word):
    pos=(0,0)
    bonds=set()
    departures=set()
    for d in word:
        dx,dy=steps[d]
        nxt=(pos[0]+dx,pos[1]+dy)
        bond=tuple(sorted((pos,nxt)))
        if bond in bonds:
            return None
        bonds.add(bond)
        departures.add(pos)
        pos=nxt
    return pos,bonds,departures

# Generate all raw words by the paper's recursion, independently of the stored map.
raw=[]
counts=[0]*11

def generate(word,code,pos,bonds,departures):
    counts[len(word)]+=1
    if len(word)==10:
        raw.append((code,word,pos,bonds,departures))
        return
    for d,(dx,dy) in enumerate(steps):
        nxt=(pos[0]+dx,pos[1]+dy)
        bond=tuple(sorted((pos,nxt)))
        if bond not in bonds:
            generate(word+(d,),4*code+d,nxt,bonds|{bond},departures|{pos})
generate((),0,(0,0),set(),set())
assert counts == [1,4,12,36,108,316,916,2628,7500,21268,60092], counts
raw_codes={x[0] for x in raw}
assert len(raw_codes)==60092
coverage_errors=[(c,a,c in raw_codes) for c,a in enumerate(classes) if (a<3741)!=(c in raw_codes)]
assert not coverage_errors, coverage_errors[:5]

representative_errors=[]
for a,c in enumerate(reps):
    if c not in raw_codes or classes[c]!=a:
        representative_errors.append((a,c,classes[c],c in raw_codes))
assert not representative_errors, representative_errors[:5]

# Regenerate every direction, kind, admitted successor and required arrival.
errors=[]
edge_counts=collections.Counter()
all_kind_mismatches=0
for code,word,pos,bonds,departures in raw:
    a=classes[code]
    repword=decode(reps[a])
    repgeo=geometry(repword)
    assert repgeo is not None
    rpos,rbonds,rdepartures=repgeo
    for d,(dx,dy) in enumerate(steps):
        nxt=(pos[0]+dx,pos[1]+dy)
        allowed=d != (word[-1]+2)%4 and tuple(sorted((pos,nxt))) not in bonds
        kind=2 if pos in departures else 0 if d==word[-1] else 1
        stored_dest=dests[a*4+d]
        stored_kind=kinds[a*4+d]
        repkind=2 if rpos in rdepartures else 0 if d==repword[-1] else 1
        if kind!=repkind:
            all_kind_mismatches+=1
        if allowed != (stored_dest != 0):
            errors.append(('allowed',code,a,d,allowed,stored_dest))
        if allowed:
            successor=encode(word[1:]+(d,))
            if stored_kind != kind:
                errors.append(('kind',code,a,d,kind,stored_kind))
            if stored_dest-1 != classes[successor]:
                errors.append(('successor',code,a,d,classes[successor],stored_dest-1))
            if kind != 2 and word[-1] != repword[-1]:
                errors.append(('arrival',code,a,d,word[-1],repword[-1]))
assert not errors, errors[:5]
for a in range(3741):
    for d in range(4):
        if dests[a*4+d]:
            edge_counts[kinds[a*4+d]]+=1
assert edge_counts=={0:2516,1:5032,2:1872},edge_counts

targets=[]
for n,lo in raw_leaves:
    i=int(n.split('_')[1])
    if i not in range(145,150):
        continue
    hi=lo+16384
    first=lo//12
    last=(hi-1)//12
    valid=[c for c in range(first,last+1) if c in raw_codes]
    full_lo=(lo+11)//12
    full_hi=hi//12
    targets.append(dict(name=n,line=lines[n],bit_start=lo,bit_end_exclusive=hi,
        first_touched_code=first,last_touched_code=last,
        wholly_contained_codes=[full_lo,full_hi-1],touched_raw_count=len(valid),
        contained_raw_count=sum(c in raw_codes for c in range(full_lo,full_hi)),
        first_raw_code=valid[0] if valid else None,last_raw_code=valid[-1] if valid else None,
        hex_sha256=hashlib.sha256(exprs[n].encode()).hexdigest(),
        integer_bits=values[n].bit_length()))
result=dict(source_sha256=hashlib.sha256(source.encode()).hexdigest(),
    table_bits=values['rawClass'].bit_length(),raw_counts_by_length=counts,
    raw_coverage_errors=len(coverage_errors),representative_errors=len(representative_errors),
    transition_errors=len(errors),representative_kind_mismatches_including_forbidden=all_kind_mismatches,
    quotient_edge_counts=dict(edge_counts),targets=targets)
Path('/home/ubuntu/aklt/reports/FID_T036/check_results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))

# Recreate the archive's natural whitespace text serialization from the Lean values.
map_rows = [f"{c} {classes[c]}" for c in sorted(raw_codes)]
class_rows = [" ".join(map(str, [reps[a]] + [v-1 for v in dests[4*a:4*a+4]] + [v if v<3 else -1 for v in kinds[4*a:4*a+4]])) for a in range(3741)]
archive_text = "60092 3741\n" + "\n".join(map_rows + class_rows) + "\n"
archive_hash = hashlib.sha256(archive_text.encode()).hexdigest()
print("RECONSTRUCTED_ARCHIVE_SHA256", archive_hash)
print("MATCHES_DECLARED_ARCHIVE", archive_hash == "671475d3333b646b3ace22a555f9a63a74f7bb076f0454f5b480c1e444a95785")
result['reconstructed_archive_sha256'] = archive_hash
result['matches_declared_archive'] = archive_hash == "671475d3333b646b3ace22a555f9a63a74f7bb076f0454f5b480c1e444a95785"
Path('/home/ubuntu/aklt/reports/FID_T036/check_results.json').write_text(json.dumps(result,indent=2)+'\n')
