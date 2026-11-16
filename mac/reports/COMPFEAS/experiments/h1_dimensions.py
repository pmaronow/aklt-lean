import sys,json,collections,math,time
from pathlib import Path
root=Path(__file__).resolve().parents[1];sys.path[:0]=[str(root/'vendor'),str(root/'programs/h1-local/code')]
import ring,cert
ring.P63=str(root/'programs/data/pext/pext7962.json');P=ring.load()
start=time.monotonic();out={}
for filename in ['certificates_covered_operator_only.jsonl','certificates_covered.jsonl']:
 recs=[json.loads(l) for l in open(root/'programs/h1-local/out'/filename)];sizes=[];multsizes=[];entrycount=0;sumk=0;maxk=0
 for r in recs:
  if r['kind']=='closed':continue
  p=ring.Pattern(P[r['pid']],refined=False);net=cert.Net(p,leafred=r['leafred']);q={(0,0):1};maxk=max(maxk,net.n);sumk+=4**net.n
  for x in ring.RING:
   ids=net.site_slots[x]
   if len(ids)==2:
    ls=[(2,0),(0,0),(-2,0)]+([(0,1)] if p.kind[x]=='d' else [])
   elif len(ids)==1:ls=[(1,0),(-1,0)]
   else:continue
   nq=collections.Counter()
   for (sz,par),cnt in q.items():
    for dz,pr in ls:nq[(sz+dz,2*par+pr)]+=cnt
   q=nq
  for par in sorted({pa for sz,pa in q}):
   sz=min([sz for sz,pa in q if pa==par],key=lambda t:(abs(t),-t));sizes.append(q[sz,par])
   for j in sorted({sz for sz,pa in q if pa==par and sz>=0}):
    mul=q.get((j,par),0)-q.get((j+2,par),0)
    assert mul>=0
    if mul:multsizes.append(mul)
 out[filename]=dict(operator_patterns=sum(r['kind']=='operator' for r in recs),blocks=len(sizes),max_size=max(sizes),matrix_entries=sum(d*d for d in sizes),pivots=sum(sizes),bareiss_updates=sum((d**3-d)//6 for d in sizes),cholesky_dot_products=sum(d*(d+1)*(d+2)//6 for d in sizes),dense_coefficients=sumk,max_slots=maxk,size_counts=dict(collections.Counter(sizes)),irrep_multiplicity_blocks=len(multsizes),irrep_max=max(multsizes),irrep_bareiss_updates=sum((d**3-d)//6 for d in multsizes),irrep_gram_products=sum(d*(d+1)*(d+2)//6 for d in multsizes))
out['wall']=time.monotonic()-start
(root/'logs/h1_dimensions.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
