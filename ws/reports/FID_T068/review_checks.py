"""Independent arithmetic and lattice reconstruction for the five assigned chunks.
Reads only the supplied Lean file; models its natural-number expressions exactly.
"""
from pathlib import Path
import ast
from collections import Counter
import hashlib
import json
import re

SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
text = SOURCE.read_text()
literals = {m[1]: int(m[2], 16) for m in re.finditer(r'private noncomputable def (\w+) : ℕ := 0x([0-9a-f]+)', text)}
line_numbers = {m[1]: text[:m.start()].count('\n')+1 for m in re.finditer(r'private noncomputable def (\w+) : ℕ := 0x', text)}

def evaluate(node):
    if isinstance(node, ast.Name):
        return literals[node.id], {node.id: 0}
    if isinstance(node, ast.Constant):
        return node.value, {}
    assert isinstance(node, ast.BinOp)
    left, lpos = evaluate(node.left)
    right, rpos = evaluate(node.right)
    if isinstance(node.op, ast.LShift):
        assert not rpos
        return left << right, {k: v+right for k, v in lpos.items()}
    assert isinstance(node.op, ast.Add)
    assert lpos.keys().isdisjoint(rpos)
    return left+right, dict(lpos, **rpos)

packs = {}
positions = {}
for name in ['rawClass', 'representatives', 'destinations', 'edgeKinds']:
    expression = re.search(r'noncomputable def '+name+r' : ℕ := ([^\n]+)', text)[1]
    packs[name], positions[name] = evaluate(ast.parse(expression.replace('<<<', '<<'), mode='eval').body)
    ordered = sorted((offset, key) for key, offset in positions[name].items())
    assert ordered[0][0] == 0
    for (offset, key), (next_offset, _) in zip(ordered, ordered[1:]):
        assert literals[key] < 1 << (next_offset-offset), (name, key, 'chunk overflow')
    assert all(key.startswith(name+'_') for _, key in ordered)
    print(name, 'chunks:', len(ordered), 'bits:', packs[name].bit_length())

# Fixed-width little-endian lane extraction is division by 2^(width*code), modulo 2^width.
def unpack(value, width, count):
    data = value.to_bytes((width*count+7)//8, 'little')
    out = []
    for i in range(count):
        bit = width*i
        offset, shift = divmod(bit, 8)
        lane = int.from_bytes(data[offset:offset+(shift+width+7)//8], 'little') >> shift
        out.append(lane & ((1 << width)-1))
    return out

class_at = unpack(packs['rawClass'], 12, 4**10)
reps = unpack(packs['representatives'], 20, 3741)
dest = unpack(packs['destinations'], 12, 3741*4)
kinds = unpack(packs['edgeKinds'], 2, 3741*4)
STEP = [(1,0), (0,1), (-1,0), (0,-1)]
def add(x,y): return x[0]+y[0], x[1]+y[1]
def bond(x,y): return tuple(sorted((x,y)))
def digits(code): return tuple((code >> (2*(9-i))) & 3 for i in range(10))
def word_string(code): return ''.join('ENWS'[d] for d in digits(code))
def geometry(code):
    w = digits(code)
    vertices = [(0,0)]
    bonds = set()
    raw = True
    for d in w:
        nxt = add(vertices[-1],STEP[d])
        b = bond(vertices[-1],nxt)
        if b in bonds: raw=False
        bonds.add(b)
        vertices.append(nxt)
    return w, vertices, bonds, raw

def row(code):
    w, vertices, bonds, raw = geometry(code)
    assert raw
    endpoint = vertices[-1]
    revisit = endpoint in vertices[:-1]
    answer = []
    for d in range(4):
        allowed = d != (w[-1]+2)%4 and bond(endpoint,add(endpoint,STEP[d])) not in bonds
        kind = 2 if revisit else (0 if d==w[-1] else 1)
        successor = ((code & ((1<<18)-1)) << 2) | d
        answer.append((allowed,kind,successor))
    return w[-1],answer

# Generate all raw windows independently, in the lexicographic order in the paper.
raw_codes=[]
counts=Counter()
def generate(depth,code,endpoint,bonds):
    counts[depth]+=1
    if depth==10:
        raw_codes.append(code)
        return
    for d, step in enumerate(STEP):
        nxt=add(endpoint,step)
        b=bond(endpoint,nxt)
        if b not in bonds:
            bonds.add(b)
            generate(depth+1,4*code+d,nxt,bonds)
            bonds.remove(b)
generate(0,0,(0,0),set())
raw_set=set(raw_codes)
print('raw counts:', [counts[i] for i in range(1,11)])
print('global class lane histogram summary:', dict(sorted(Counter('class' if x<3741 else ('sentinel' if x==3741 else 'out-of-range') for x in class_at).items())))
print('global coverage mismatches:', sum((v<3741)!=(code in raw_set) for code,v in enumerate(class_at)))
print('representatives invalid/out-of-range:',sum(x>=4**10 or x not in raw_set for x in reps))
print('representatives not mapping to own class:',sum(class_at[x]!=a for a,x in enumerate(reps)))
print('edge counts:',dict(sorted(Counter(kinds[i] for i in range(3741*4) if dest[i]).items())))
print('edge encoding violations:',sum(not(0<=dest[i]<=3741 and ((dest[i]==0)==(kinds[i]==3))) for i in range(3741*4)))

# Audit all raw state rows, then attribute any affected rows to the assigned chunks.
rep_rows=[row(x) for x in reps]
errors={}
for code in raw_codes:
    a=class_at[code]
    err=[]
    if not a<3741:
        err.append('raw word mapped to sentinel')
    else:
        arrival,steps=row(code)
        for d,(allowed,kind,successor) in enumerate(steps):
            idx=4*a+d
            if bool(dest[idx])!=allowed: err.append(f'{"ENWS"[d]} admissibility')
            if rep_rows[a][1][d][1]!=kind: err.append(f'{"ENWS"[d]} representative kind')
            if allowed:
                if kinds[idx]!=kind: err.append(f'{"ENWS"[d]} kind')
                if dest[idx]-1!=class_at[successor]: err.append(f'{"ENWS"[d]} successor')
                if kind!=2 and arrival!=(reps[a]%4): err.append(f'{"ENWS"[d]} arrival')
    if err: errors[code]=err
print('global raw row failures (including kind on inadmissible directions):',len(errors))
assert counts[10] == 60092
assert not errors
assert all((v<3741)==(code in raw_set) and v<=3741 for code,v in enumerate(class_at))
assert all(x in raw_set and class_at[x]==a for a,x in enumerate(reps))
assert all(0<=dest[i]<=3741 and ((dest[i]==0)==(kinds[i]==3)) for i in range(3741*4))
assert Counter(kinds[i] for i in range(3741*4) if dest[i]) == {0:2516,1:5032,2:1872}

report=[]
for k in range(305,310):
    key=f'rawClass_{k}'
    start=positions['rawClass'][key]
    higher=[o for o in positions['rawClass'].values() if o>start]
    stop=min(higher) if higher else 12*4**10
    first=start//12
    last=(stop-1)//12
    relevant=range(first,last+1)
    covered_raw=[x for x in relevant if x in raw_set]
    coverage=[x for x in relevant if (class_at[x]<3741)!=(x in raw_set) or class_at[x]>3741]
    failures=[x for x in relevant if x in errors]
    item={'declaration':key,'line':line_numbers[key],'bit_interval':[start,stop],
          'code_interval':[first,last], 'boundary_bits':[start%12,stop%12],
          'raw_words':len(covered_raw),'nonraw_words':len(relevant)-len(covered_raw),
          'coverage_failures':coverage,'row_failure_count':len(failures),
          'first_failures':[{'code':x,'word':word_string(x),'class':class_at[x],
                             'representative_code':reps[class_at[x]],
                             'representative':word_string(reps[class_at[x]]),'errors':errors[x]}
                            for x in failures[:5]],
          'sha256_hex_literal':hashlib.sha256(re.search(r'private noncomputable def '+key+r' : ℕ := 0x([0-9a-f]+)',text)[1].encode()).hexdigest()}
    report.append(item)
    print(json.dumps(item,sort_keys=True))
Path('check_results.json').write_text(json.dumps(report,indent=2)+'\n')
