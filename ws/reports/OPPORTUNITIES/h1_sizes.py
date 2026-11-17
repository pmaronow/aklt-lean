"""Count actual exchange blocks and potential highest-weight blocks, no operator claims."""
import ast
import collections
import itertools
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parent
B=Path('/home/ubuntu/aklt/manuscript/bundle/programs')
patterns=json.loads((B/'data/pext/pext7962.json').read_text())

def groups(r,reduced):
    kinds={ast.literal_eval(k):v for k,v in r['kinds'].items()}
    edges=[set(map(tuple,e)) for e in r['present']]
    ans=[]
    for x in [(1,0),(0,1),(-1,0),(0,-1)]:
        if {x,(2*x[0],2*x[1])} in edges: ans.append('s')
    for x in [(1,1),(-1,1),(-1,-1),(1,-1)]:
        deg=sum(x in e for e in edges)
        if deg: ans.append('s' if reduced and deg==1 else kinds[x])
    return ans

def blocks(gr):
    d=gr.count('d'); allblocks=[]; highest=[]
    for eps in itertools.product((True,False),repeat=d):
        signs=iter(eps); weight={0:1}
        for g in gr:
            ws=(1,-1) if g=='s' else (2,0,-2)
            if g=='d' and not next(signs): ws=(0,)
            nw=collections.Counter()
            for a,n in weight.items():
                for b in ws: nw[a+b]+=n
            weight=nw
        parity=gr.count('s')%2
        allblocks.append(weight.get(parity,0))
        for j in range(parity,max(weight)+1,2):
            mult=weight.get(j,0)-weight.get(j+2,0)
            if mult: highest.append(mult)
    return allblocks,highest

def summary(dims):
    return dict(blocks=len(dims),maximum=max(dims),entries=sum(n*n for n in dims),
        upper_Bareiss_updates=sum(n*(n-1)*(n+1)//6 for n in dims),
        full_Bareiss_updates=sum(n*(n-1)*(2*n-1)//6 for n in dims))

out={}
for name in ['certificates_covered','certificates_covered_operator_only']:
    records=[json.loads(l) for l in (B/f'h1-local/out/{name}.jsonl').read_text().splitlines()]
    dims=[];hw=[]
    for r in records:
        if r['kind']!='operator':continue
        a,b=blocks(groups(patterns[r['pid']],r['leafred']));dims+=a;hw+=b
    out[name]=dict(operator_patterns=sum(r['kind']=='operator' for r in records),
                   central=summary(dims),highest_weight=summary(hw))
(ROOT/'experiments/h1_sizes.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
