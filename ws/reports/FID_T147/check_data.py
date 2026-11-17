from pathlib import Path
import re, json, hashlib
from collections import Counter

SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
s = SOURCE.read_text()
literals = {name: int(value,16) for name,value in re.findall(r'private noncomputable def (\w+) : ℕ := 0x([0-9a-f]+)',s)}

def parse_table(name):
    expression = re.search(r'^noncomputable def '+name+r' : ℕ := (.*)$',s,re.M)[1]
    tokens = re.findall(r'\w+|<<<|[()+]', expression)
    assert ''.join(tokens) == re.sub(r'\s+','',expression)
    pos = 0
    def atom():
        nonlocal pos
        token=tokens[pos];pos+=1
        if token=='(':
            tree=expr()
            assert tokens[pos]==')';pos+=1
            return tree
        assert token in literals
        return ('leaf',token)
    def add():
        nonlocal pos
        tree=atom()
        while pos<len(tokens) and tokens[pos]=='+':
            pos+=1;tree=('add',tree,atom())
        return tree
    def expr():
        nonlocal pos
        tree=add()
        while pos<len(tokens) and tokens[pos]=='<<<':
            pos+=1
            shift=int(tokens[pos]);pos+=1
            tree=('shift',tree,shift)
        return tree
    tree=expr();assert pos==len(tokens)
    leaves=[]
    def collect(t,offset=0):
        if t[0]=='leaf':leaves.append((offset,t[1],literals[t[1]]))
        elif t[0]=='add':collect(t[1],offset);collect(t[2],offset)
        else:collect(t[1],offset+t[2])
    collect(tree)
    leaves.sort()
    value=0
    for i,(offset,leaf,number) in enumerate(leaves):
        if i+1<len(leaves):assert number.bit_length()<=leaves[i+1][0]-offset
        value+=number<<offset
    return value,leaves

tables={name:parse_table(name) for name in ('rawClass','representatives','destinations','edgeKinds')}
raw_number,raw_leaves=tables['rawClass']
raw_bytes=raw_number.to_bytes(12*4**10//8,'little')
def raw(code):
    byte,bit=divmod(12*code,8)
    return (int.from_bytes(raw_bytes[byte:byte+2],'little')>>bit)&4095

def lane(table,width,index):return (tables[table][0]>>(width*index))&((1<<width)-1)
def rep(a):return lane('representatives',20,a)
def destination(a,d):return lane('destinations',12,4*a+d)
def kind(a,d):return lane('edgeKinds',2,4*a+d)

steps=((1,0),(0,1),(-1,0),(0,-1))
def plus(x,y):return x[0]+y[0],x[1]+y[1]
def bond(x,y):return tuple(sorted((x,y)))
# Generate all windows independently, by the paper's unused-unoriented-bond recursion.
states={}
counts=[0]*11
def generate(ds,vertices,bonds,code):
    depth=len(ds);counts[depth]+=1
    if depth==10:
        states[code]=(ds,vertices,bonds)
        return
    x=vertices[-1]
    for d,step in enumerate(steps):
        y=plus(x,step);edge=bond(x,y)
        if edge not in bonds:generate(ds+(d,),vertices+(y,),bonds|{edge},4*code+d)
generate((),((0,0),),frozenset(),0)
assert counts[1:]==[4,12,36,108,316,916,2628,7500,21268,60092]
coverage=[]
for code in range(4**10):
    a=raw(code)
    if not (a<=3741 and (a<3741)==(code in states)):coverage.append((code,a,code in states))
assert not coverage,coverage[:5]
assert {raw(code) for code in states}==set(range(3741))
representative_errors=[]
for a in range(3741):
    code=rep(a)
    if not(code<4**10 and code in states and raw(code)==a):representative_errors.append((a,code,raw(code)))
assert not representative_errors,representative_errors[:5]

def row(code):
    ds,vertices,bonds=states[code]
    x=vertices[-1];revisit=x in vertices[:-1]
    out=[]
    for d,step in enumerate(steps):
        allowed=d!=(ds[-1]+2)%4 and bond(x,plus(x,step)) not in bonds
        k=2 if revisit else 0 if d==ds[-1] else 1
        nxt=(code%(4**9))*4+d
        out.append((allowed,k,nxt))
    return out
rep_rows=[row(rep(a)) for a in range(3741)]
errors=[];all_kind_errors=[]
for code in states:
    a=raw(code)
    for d,(allowed,k,nxt) in enumerate(row(code)):
        dest=destination(a,d);stored_kind=kind(a,d)
        rep_allowed,rep_kind,_=rep_rows[a][d]
        if k!=rep_kind:all_kind_errors.append((code,a,d,k,rep_kind))
        if not (dest<=3741 and (dest==0)==(stored_kind==3) and (dest==0 or stored_kind<3)):
            errors.append(('encoding',code,a,d,dest,stored_kind))
        if allowed!=(dest!=0) or allowed!=rep_allowed:
            errors.append(('allowed',code,a,d,allowed,dest))
        if allowed:
            if nxt not in states:errors.append(('successor raw',code,d,nxt))
            if k!=stored_kind:errors.append(('kind',code,a,d,k,stored_kind))
            if raw(nxt)!=dest-1:errors.append(('successor',code,a,d,nxt,raw(nxt),dest))
            if k!=2 and (rep(a)%4)!=(code%4):errors.append(('arrival',code,a,d))
assert not errors,errors[:5]
assert not all_kind_errors,all_kind_errors[:5]
edge_counts=Counter(kind(a,d) for a in range(3741) for d in range(4) if destination(a,d)!=0)
assert edge_counts=={0:2516,1:5032,2:1872},edge_counts

chunks=[]
for i in range(700,705):
    name=f'rawClass_{i}'
    offset,_,number=next(x for x in raw_leaves if x[1]==name)
    width=next(x[0] for x in raw_leaves if x[0]>offset)-offset
    start=offset//12;end=(offset+width-1)//12
    touched=[c for c in range(start,end+1) if c in states]
    fully=[c for c in range(start,end+1) if 12*c>=offset and 12*(c+1)<=offset+width]
    valid_fully=[c for c in fully if c in states]
    examples=[{'code':c,'word':''.join('ENWS'[d] for d in states[c][0]),'class':raw(c)} for c in touched[:3]]
    chunks.append({'declaration':name,'line':next(n for n,l in enumerate(s.splitlines(),1) if l.startswith('private noncomputable def '+name+' ')), 'offset':offset,'width':width,'bits_in_first_lane':12-offset%12 if offset%12 else 12,'code_first':start,'code_last':end,'complete_lanes':len(fully),'complete_raw_lanes':len(valid_fully),'complete_nonraw_lanes':len(fully)-len(valid_fully),'touched_raw_lanes':len(touched),'class_min':min(map(raw,touched),default=None),'class_max':max(map(raw,touched),default=None),'examples':examples})
result={'source_sha256':hashlib.sha256(s.encode()).hexdigest(),'raw_counts_by_length':counts[1:],'total_lanes':4**10,'valid_lanes':len(states),'invalid_lanes':4**10-len(states),'classes':3741,'edge_counts':dict(edge_counts),'coverage_errors':len(coverage),'quotient_errors':len(errors),'kind_agreement_including_forbidden_errors':len(all_kind_errors),'chunks':chunks}
Path('/home/ubuntu/aklt/reports/FID_T147/check_results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
