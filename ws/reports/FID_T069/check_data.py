from pathlib import Path
import ast, re, collections, json

SOURCE=Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
source=SOURCE.read_text()
values={}
lengths={}
for family,index,h in re.findall(r'private noncomputable def (rawClass|representatives|destinations|edgeKinds)_(\d+) : ℕ := 0x([0-9a-f]+)',source):
    name=f'{family}_{index}'
    values[name]=int(h,16)
    lengths[name]=4*len(h)

def parse_expr(family):
    expr=re.search(r'^noncomputable def '+family+r' : ℕ := (.+)$',source,re.M)[1]
    return ast.parse(expr.replace('<<<','<<'),mode='eval').body

def evaluate(node):
    if isinstance(node,ast.Name): return values[node.id]
    if isinstance(node,ast.Constant) and type(node.value) is int: return node.value
    if isinstance(node,ast.BinOp):
        a,b=evaluate(node.left),evaluate(node.right)
        if isinstance(node.op,ast.Add): return a+b
        if isinstance(node.op,ast.LShift): return a<<b
    raise ValueError(ast.dump(node))

def pieces(node,offset=0):
    if isinstance(node,ast.Name): return [(node.id,offset)]
    if isinstance(node,ast.BinOp):
        if isinstance(node.op,ast.Add): return pieces(node.left,offset)+pieces(node.right,offset)
        if isinstance(node.op,ast.LShift): return pieces(node.left,offset+evaluate(node.right))
    raise ValueError(ast.dump(node))

packed={family:evaluate(parse_expr(family)) for family in ['rawClass','representatives','destinations','edgeKinds']}
raw_pieces=dict(pieces(parse_expr('rawClass')))
for family,p in packed.items(): print('PACKED',family,'bit_length',p.bit_length())
for i in range(310,315):
    name=f'rawClass_{i}'; lo=raw_pieces[name]; hi=lo+lengths[name]
    print('PIECE',name,'source_line',next(n for n,s in enumerate(source.splitlines(),1) if s.startswith('private noncomputable def '+name+' :')),'bit_range',[lo,hi],'code_range',[lo//12,(hi-1)//12],'edge_bit_offsets',[lo%12,hi%12])
ordered=sorted((offset,name) for name,offset in raw_pieces.items())
assert len(ordered)==768 and ordered[0][0]==0
assert all(offset+lengths[name]==offset2 for (offset,name),(offset2,_) in zip(ordered,ordered[1:]))
print('PACKING: all 768 rawClass pieces fit contiguously without overlap')
# Fixed-width extraction reproduces Lean Nat division and modulo.
raw_bytes=packed['rawClass'].to_bytes((packed['rawClass'].bit_length()+7)//8,'little')
def lane(family,width,index):
    if family=='rawClass':
        k=width*index; j=k//8
        return (int.from_bytes(raw_bytes[j:j+3],'little')>>(k%8))&((1<<width)-1)
    return (packed[family]>>(width*index))&((1<<width)-1)

def word(code,m=10): return tuple((code>>(2*(m-1-i)))&3 for i in range(m))
STEPS=((1,0),(0,1),(-1,0),(0,-1))
def path(ds):
    x=(0,0); vertices=[x]; bonds=[]
    for d in ds:
        v=STEPS[d]; y=(x[0]+v[0],x[1]+v[1])
        bonds.append(tuple(sorted((x,y)))); vertices.append(y); x=y
    return vertices,bonds

def raw(ds):
    vs,bs=path(ds)
    return len(bs)==len(set(bs))

def row(ds):
    vs,bs=path(ds); x=vs[-1]; revisit=x in vs[:-1]
    ans=[]
    for d,v in enumerate(STEPS):
        y=(x[0]+v[0],x[1]+v[1]); bond=tuple(sorted((x,y)))
        allowed=d!=(ds[-1]+2)%4 and bond not in bs
        kind=2 if revisit else (0 if d==ds[-1] else 1)
        ans.append((allowed,kind))
    return ans

# Generate exactly the distinct-unoriented-bond recursion in the paper.
raw_codes=[]
counts=collections.Counter()
def generate(ds,code,x,bonds):
    counts[len(ds)]+=1
    if len(ds)==10:
        raw_codes.append(code); return
    for d,v in enumerate(STEPS):
        y=(x[0]+v[0],x[1]+v[1]); bond=tuple(sorted((x,y)))
        if bond not in bonds: generate(ds+(d,),4*code+d,y,bonds|{bond})
generate((),0,(0,0),set())
assert raw_codes==sorted(set(raw_codes))
print('COUNTS',dict(sorted(counts.items())))
raw_set=set(raw_codes)
errors=[]
for code in range(4**10):
    a=lane('rawClass',12,code)
    if a>3741 or ((a<3741)!=(code in raw_set)):
        errors.append((code,a,code in raw_set))
print('COVERAGE_ERRORS',len(errors),errors[:25])

reps=[lane('representatives',20,a) for a in range(3741)]
rep_errors=[(a,c,lane('rawClass',12,c),raw(word(c))) for a,c in enumerate(reps) if c>=4**10 or c not in raw_set or lane('rawClass',12,c)!=a]
print('REP_ERRORS',len(rep_errors),rep_errors[:25])
row_errors=[]
edge_counts=collections.Counter()
for a,c in enumerate(reps):
    for d,(ad,ki) in enumerate(row(word(c))):
        destination=lane('destinations',12,4*a+d)
        kind=lane('edgeKinds',2,4*a+d)
        if destination>3741 or ((destination==0)!=(kind==3)) or (destination!=0 and kind>=3): row_errors.append(('bounds',a,d,destination,kind))
        if (destination!=0)!=ad: row_errors.append(('allowed',a,d,destination,ad))
        if ad:
            edge_counts[kind]+=1
            actual=lane('rawClass',12,((c%(4**9))*4+d))
            if kind!=ki or destination-1!=actual: row_errors.append(('kind_successor',a,d,kind,ki,destination-1,actual))
print('REP_ROW_ERRORS',len(row_errors),row_errors[:25]); print('EDGE_COUNTS',dict(edge_counts))

class_errors=[]
for code in raw_codes:
    a=lane('rawClass',12,code)
    if a>=3741: class_errors.append(('range',code,a)); continue
    ds=word(code); rc=reps[a]; rds=word(rc)
    for d,((ad,ki),(rad,rki)) in enumerate(zip(row(ds),row(rds))):
        if ad!=rad or ki!=rki: class_errors.append(('compatible',code,a,rc,d,ad,rad,ki,rki))
        if ad:
            destination=lane('destinations',12,4*a+d)-1
            successor=lane('rawClass',12,(code%(4**9))*4+d)
            if destination!=successor: class_errors.append(('successor',code,a,rc,d,destination,successor))
            if ki!=2 and ds[-1]!=rds[-1]: class_errors.append(('arrival',code,a,rc,d,ds[-1],rds[-1]))
print('CLASS_ERRORS',len(class_errors),class_errors[:25])

for i in range(310,315):
    name=f'rawClass_{i}'; lo=raw_pieces[name]; hi=lo+lengths[name]
    code_lo,code_hi=lo//12,(hi-1)//12
    affected=range(code_lo,code_hi+1)
    print('ASSIGNED',name,'raw words',sum(c in raw_set for c in affected),'value_counts',dict(collections.Counter(lane('rawClass',12,c) for c in affected)),'coverage_errors',[e for e in errors if code_lo<=e[0]<=code_hi],'class_errors',[e for e in class_errors if isinstance(e[1],int) and code_lo<=e[1]<=code_hi][:25])
    print('BOUNDARIES',[(c,lane('rawClass',12,c),''.join('ENWS'[d] for d in word(c)),raw(word(c))) for c in [code_lo-1,code_lo,code_hi,code_hi+1]])
