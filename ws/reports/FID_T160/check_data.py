"""Read-only reconstruction of Automaton10Data and the paper's trail contract."""
import ast
from collections import Counter
from pathlib import Path
import re

ROOT = Path('/home/ubuntu/aklt/review/FID_T/lean')
SOURCE = ROOT / 'AKLT/Defs/Automaton10Data.lean'
text = SOURCE.read_text()
values = {}
trees = {}
locations = {}

def evaluate(node):
    if isinstance(node, ast.Name):
        return values[node.id]
    if isinstance(node, ast.Constant) and isinstance(node.value, int):
        return node.value
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add):
        return evaluate(node.left) + evaluate(node.right)
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.LShift):
        return evaluate(node.left) << evaluate(node.right)
    raise ValueError(ast.dump(node))

for lineno, line in enumerate(text.splitlines(), 1):
    match = re.fullmatch(r'(?:private )?noncomputable def (\w+) : ℕ := (.*)', line)
    if not match:
        continue
    name, expression = match.groups()
    tree = ast.parse(expression.replace('<<<', '<<'), mode='eval').body
    trees[name] = tree
    locations[name] = lineno
    values[name] = evaluate(tree)

def offsets(node, base=0):
    if isinstance(node, ast.Name):
        return [(node.id, base)]
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add):
        return offsets(node.left, base) + offsets(node.right, base)
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.LShift):
        return offsets(node.left, base + evaluate(node.right))
    raise ValueError(ast.dump(node))

def unpack(name, width, count):
    packed = values[name]
    data = packed.to_bytes((width * count + 7) // 8, 'little')
    mask = (1 << width) - 1
    # The table widths divide a small multiple of eight.
    return [
        (int.from_bytes(data[width*i//8:(width*(i+1)+7)//8], 'little') >> (width*i % 8)) & mask
        for i in range(count)
    ]

raw = unpack('rawClass', 12, 4**10)
reps = unpack('representatives', 20, 3741)
dests = unpack('destinations', 12, 3741*4)
kinds = unpack('edgeKinds', 2, 3741*4)
print('Parsed all', len(values), 'natural-number data declarations.')
for table, width, count in [('rawClass',12,4**10),('representatives',20,3741),('destinations',12,3741*4),('edgeKinds',2,3741*4)]:
    spans = sorted((offset, name) for name, offset in offsets(trees[table]))
    errors = []
    for index, (offset, name) in enumerate(spans):
        boundary = spans[index+1][0] if index+1 < len(spans) else width*count
        if offset + values[name].bit_length() > boundary:
            errors.append((name, offset, boundary, values[name].bit_length()))
    print('PACK', table, 'bits', values[table].bit_length(), 'capacity', width*count,
          'leaves', len(spans), 'overflows', errors)
    assert not errors
    assert spans[0][0] == 0
    assert len({name for _,name in spans}) == len(spans)
    assert values[table] < 1 << (width*count)
    for offset, name in spans:
        if name in {'rawClass_765','rawClass_766','rawClass_767','representatives_0'}:
            print('TARGET', name, 'line', locations[name], 'offset', offset,
                  'bits', values[name].bit_length(), 'lane quotient/remainder', divmod(offset,width))
print('raw lane histogram:', sorted(Counter(raw).items())[:4], '...',
      sorted(Counter(raw).items())[-4:])
print('raw lane range:', min(raw), max(raw), 'sentinels:', raw.count(3741))

STEPS = [(1,0),(0,1),(-1,0),(0,-1)]
counts = [0]*11
words = {}
used = set()
word = []

def bond(p,q):
    return tuple(sorted((p,q)))

def generate(depth, position, code):
    counts[depth] += 1
    if depth == 10:
        words[code] = tuple(word)
        return
    x,y = position
    for d,(dx,dy) in enumerate(STEPS):
        q = (x+dx,y+dy)
        edge = bond(position,q)
        if edge in used:
            continue
        used.add(edge)
        word.append(d)
        generate(depth+1,q,4*code+d)
        word.pop()
        used.remove(edge)

generate(0,(0,0),0)
print('Independent raw counts:', counts)
missing = [code for code in words if raw[code] >= 3741]
extra = [code for code,value in enumerate(raw) if value < 3741 and code not in words]
out_of_range = [(code,value) for code,value in enumerate(raw) if value > 3741]
print('COVERAGE missing',len(missing), missing[:10], 'extra',len(extra), extra[:10],
      'out of range',len(out_of_range),out_of_range[:10])

def decode(code):
    return tuple((code >> (2*(9-i))) & 3 for i in range(10))

def properties(w):
    position = (0,0)
    departures = set()
    bonds = set()
    for d in w:
        departures.add(position)
        dx,dy = STEPS[d]
        q = (position[0]+dx,position[1]+dy)
        bonds.add(bond(position,q))
        position=q
    revisit = position in departures
    result=[]
    for d,(dx,dy) in enumerate(STEPS):
        q=(position[0]+dx,position[1]+dy)
        allowed = d != (w[-1]+2)%4 and bond(position,q) not in bonds
        kind = 2 if revisit else (0 if d==w[-1] else 1)
        result.append((allowed,kind))
    return result

rep_errors=[]
for a,code in enumerate(reps):
    if code>=4**10 or code not in words or raw[code]!=a:
        rep_errors.append((a,code,raw[code] if code<4**10 else None,code in words))
print('REPRESENTATIVES errors',len(rep_errors),rep_errors[:10], 'distinct',len(set(reps)),
      'code range',min(reps),max(reps))

row_errors=[]
edge_counts=Counter()
for a,code in enumerate(reps):
    for d,(allowed,kind) in enumerate(properties(decode(code))):
        idx=4*a+d
        if dests[idx]>3741 or ((dests[idx]==0)!=(kinds[idx]==3)):
            row_errors.append(('encoding',a,d,dests[idx],kinds[idx]))
        if (dests[idx]!=0)!=allowed or (allowed and kinds[idx]!=kind):
            row_errors.append(('rawrow',a,d,dests[idx],kinds[idx],allowed,kind))
        if allowed:
            successor=((code % 4**9)*4+d)
            if dests[idx]-1!=raw[successor]:
                row_errors.append(('successor',a,d,dests[idx]-1,raw[successor]))
            edge_counts[kind]+=1
print('REPRESENTATIVE ROW errors',len(row_errors),row_errors[:10], 'edge counts',dict(edge_counts))

errors=Counter()
examples={}
seen_classes=set()
target_ranges=[]
for name,offset in offsets(trees['rawClass']):
    if name in {'rawClass_765','rawClass_766','rawClass_767'}:
        target_ranges.append((name,offset,offset+values[name].bit_length()))
target_stats={name:Counter() for name,_,_ in target_ranges}
for code,w in words.items():
    a=raw[code]
    if a>=3741:
        continue
    seen_classes.add(a)
    rep_properties=properties(decode(reps[a]))
    for d,(allowed,kind) in enumerate(properties(w)):
        idx=4*a+d
        tests={
            'admissibility': (dests[idx]!=0)==allowed,
            'kind_all_directions': rep_properties[d][1]==kind,
            'admitted_kind': not allowed or kinds[idx]==kind,
            'successor': not allowed or dests[idx]-1==raw[(code % 4**9)*4+d],
            'nonrevisit_arrival': not allowed or kind==2 or w[-1]==(reps[a]%4),
        }
        for key,ok in tests.items():
            if not ok:
                errors[key]+=1
                examples.setdefault(key,(code,a,d,reps[a],dests[idx],kinds[idx],allowed,kind))
    for name,lo,hi in target_ranges:
        if 12*code<hi and 12*(code+1)>lo:
            target_stats[name]['raw_windows']+=1
print('ALL RAW ROW errors',dict(errors),'examples',examples,'covered classes',len(seen_classes))
for name,lo,hi in target_ranges:
    first=lo//12
    last=(hi-1)//12
    print('TARGET COVERAGE',name,'codes',first,last,'raw windows',dict(target_stats[name]),
          'first lanes',[(i,raw[i]) for i in range(first,min(first+3,last+1))])
rep_offset = dict(offsets(trees['representatives']))['representatives_0']
rep_first = rep_offset//20
print('First representative lane touching representatives_0:',rep_first,
      'values around boundary',[(i,reps[i]) for i in range(rep_first-1,rep_first+3)])
print('Representative lanes touching representatives_0:', len(reps)-rep_first,
      'range',rep_first,len(reps)-1)

if __name__=='__main__':
    assert counts[1:]==[4,12,36,108,316,916,2628,7500,21268,60092]
    assert not missing and not extra and not out_of_range
    assert not rep_errors and not row_errors and not errors
    assert len(seen_classes)==3741
    assert edge_counts=={0:2516,1:5032,2:1872}
