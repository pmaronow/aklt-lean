from pathlib import Path
from collections import Counter
import re,json,hashlib

BASE=Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs')
source=(BASE/'Automaton10Data.lean').read_text()
literals={name:int(value,16) for name,value in re.findall(r'^private noncomputable def (\w+) : ℕ := 0x([0-9a-f]+)$',source,re.M)}

# Every operation in the four generated packing expressions is explicitly
# parenthesized. Parse those expressions, preserving the Lean expression tree.
def parse_packing(expression):
    tokens=re.findall(r'<<<|\w+|[()+]',expression)
    assert ''.join(tokens)==re.sub(r'\s+','',expression)
    position=0
    def expr():
        nonlocal position
        if tokens[position]=='(':
            position+=1
            left=expr()
            while tokens[position]!=')':
                op=tokens[position];position+=1
                right=expr()
                left=(op,left,right)
            position+=1
            return left
        token=tokens[position];position+=1
        return int(token) if token.isdecimal() else token
    tree=expr()
    assert position==len(tokens)
    return tree

def evaluate(tree):
    if isinstance(tree,int): return tree
    if isinstance(tree,str): return literals[tree]
    op,a,b=tree
    if op=='+': return evaluate(a)+evaluate(b)
    assert op=='<<<'
    return evaluate(a)<<evaluate(b)

def leaves(tree,offset=0):
    if isinstance(tree,str): return [(tree,offset)]
    assert not isinstance(tree,int)
    op,a,b=tree
    if op=='+': return leaves(a,offset)+leaves(b,offset)
    assert op=='<<<' and isinstance(b,int)
    return leaves(a,offset+b)

def lanes(value,width,count):
    octets=value.to_bytes((width*count+7)//8,'little')
    mask=(1<<width)-1
    # Read only bytes covering a lane; avoids repeated division of the giant table.
    return [(int.from_bytes(octets[(width*i)//8:(width*i+width+7)//8],'little') >> ((width*i)%8)) & mask for i in range(count)]

tables={}
trees={}
for name,width,count in [('rawClass',12,4**10),('representatives',20,3741),('destinations',12,3741*4),('edgeKinds',2,3741*4)]:
    expression=re.search(r'^noncomputable def '+name+r' : ℕ := (.+)$',source,re.M)[1]
    tree=parse_packing(expression);trees[name]=tree
    number=evaluate(tree)
    tables[name]=lanes(number,width,count)
    offsets=sorted((offset,literals[leaf].bit_length(),leaf) for leaf,offset in leaves(tree))
    assert len(set(leaf for _,_,leaf in offsets))==len(offsets)
    assert all(offset+bits<=offsets[i+1][0] for i,(offset,bits,_) in enumerate(offsets[:-1]))
    print(name, 'lanes',count,'bits',number.bit_length(),'max',max(tables[name]),'non-overlapping chunks',len(offsets))
raw=tables['rawClass'];reps=tables['representatives'];dest=tables['destinations'];kinds=tables['edgeKinds']
print('raw counts',Counter(raw).most_common(4),'invalid',raw.count(3741),'valid',sum(x<3741 for x in raw))
assert all(0<=v<=3741 for v in raw)

step=((1,0),(0,1),(-1,0),(0,-1))
def word(code): return tuple((code>>(2*j))&3 for j in reversed(range(10)))
def path(code):
    directions=word(code);vertices=[(0,0)];bonds=[]
    for d in directions:
        x,y=vertices[-1];dx,dy=step[d]
        v=(x+dx,y+dy)
        bonds.append(tuple(sorted((vertices[-1],v))))
        vertices.append(v)
    return directions,vertices,bonds

counts=[0]*11
valid={}
def generate(directions,vertices,bonds,code):
    depth=len(directions);counts[depth]+=1
    if depth==10:
        valid[code]=(directions,vertices,bonds)
        return
    x,y=vertices[-1]
    for d,(dx,dy) in enumerate(step):
        v=(x+dx,y+dy);bond=tuple(sorted(((x,y),v)))
        if bond not in bonds:
            generate(directions+(d,),vertices+(v,),bonds|{bond},code*4+d)
generate((),((0,0),),frozenset(),0)
print('Regenerated counts by depth:',counts)
assert counts==[1,4,12,36,108,316,916,2628,7500,21268,60092]
valid_set=set(valid)
assert all((v<3741)==(c in valid_set) for c,v in enumerate(raw))
print('Coverage across all 4^10 codes: PASS')
assert len(reps)==3741 and max(reps)<4**10
assert all(c in valid and raw[c]==a for a,c in enumerate(reps))
print('All representative validity, own-class and surjectivity checks: PASS')
assert all(0<=v<=3741 for v in dest)
assert all((v==0)==(k==3) for v,k in zip(dest,kinds))
print('Successor/kind bounds and sentinels: PASS')

# Compare raw windows with their class representatives and stored rows.
# Kinds are compared on all four directions, including inadmissible ones,
# to cover the paper lemma's stronger reading as well.
checks=Counter();failures=[]
for code,(directions,vertices,bonds) in valid.items():
    a=raw[code];arrival=directions[-1];end=vertices[-1]
    repdirs,repverts,repbonds=valid[reps[a]]
    repend=repverts[-1];reparrival=repdirs[-1]
    revisit=end in vertices[:-1];reprev=repend in repverts[:-1]
    for d,(dx,dy) in enumerate(step):
        admissible=d!=(arrival+2)%4 and tuple(sorted((end,(end[0]+dx,end[1]+dy)))) not in bonds
        repadmissible=d!=(reparrival+2)%4 and tuple(sorted((repend,(repend[0]+dx,repend[1]+dy)))) not in repbonds
        kind=2 if revisit else (0 if d==arrival else 1)
        repkind=2 if reprev else (0 if d==reparrival else 1)
        checks['admissibility']+=1
        if not (admissible==repadmissible==(dest[4*a+d]!=0)):
            failures.append(('admissibility',code,a,d))
        checks['kind_all_directions']+=1
        if kind!=repkind: failures.append(('kind-representative',code,a,d))
        if admissible:
            checks['admitted_kind_successor']+=1
            successor=(code%(4**9))*4+d
            if kinds[4*a+d]!=kind or dest[4*a+d]-1!=raw[successor]:
                failures.append(('stored_kind_successor',code,a,d,successor))
            if kind!=2:
                checks['nonrevisit_arrival']+=1
                if arrival!=reparrival: failures.append(('arrival',code,a,d))
print('All raw-to-quotient comparisons:',dict(checks),'failures',len(failures),failures[:10])
assert not failures
edge_counts=Counter(k for v,k in zip(dest,kinds) if v)
print('Quotient edge counts (0=straight,1=turn,2=revisit):',dict(edge_counts))
assert edge_counts=={0:2516,1:5032,2:1872}

# Repack a corrected table independently to verify every bit of each target.
# The complete lane table is also checked for the raw coverage and compatibility
# properties above; numerical class labels are fixed by supplied representatives.
rawleaves=dict(leaves(trees['rawClass']))
summaries=[]
for j in range(35,40):
    name=f'rawClass_{j}';offset=rawleaves[name]
    width=16384
    first=offset//12;last=(offset+width-1)//12
    touched=range(first,last+1)
    selected=[c for c in touched if c in valid]
    # Slice the reconstructed 12-bit lanes, including both partial boundary lanes.
    reconstructed=sum(raw[c]<<(12*(c-first)) for c in touched)
    exact=(reconstructed>>(offset-12*first))&((1<<width)-1)
    assert exact==literals[name]
    info={'name':name,'offset':offset,'bits':width,'code_first':first,'code_last':last,
          'start_bit_in_first_lane':offset%12,'valid_lanes_touched':len(selected),
          'invalid_lanes_touched':len(touched)-len(selected),
          'classes_touched':len({raw[c] for c in selected}),
          'first_valid':None if not selected else {'code':selected[0],'word':''.join('ENWS'[d] for d in word(selected[0])),'class':raw[selected[0]]},
          'last_valid':None if not selected else {'code':selected[-1],'word':''.join('ENWS'[d] for d in word(selected[-1])),'class':raw[selected[-1]]},
          'sha256_hex':hashlib.sha256(format(literals[name],'x').encode()).hexdigest()}
    summaries.append(info)
    print('TARGET',json.dumps(info))
Path('/home/ubuntu/aklt/reports/FID_T014/check_results.json').write_text(json.dumps({'depth_counts':counts,'comparisons':dict(checks),'edges':dict(edge_counts),'targets':summaries},indent=2)+'\n')
print('PASS: all finite reconstruction checks')
