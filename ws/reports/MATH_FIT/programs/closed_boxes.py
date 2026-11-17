import sys,json,collections,math
from fractions import Fraction as F
sys.path.insert(0,'/home/ubuntu/aklt/compfeas/programs/h1-local/code')
import ring
from closed_exact import radii_exact,certify_decoupled
from collapse import gram_min
P=json.load(open('/home/ubuntu/aklt/compfeas/programs/data/pext/pext7962.json'))
g={False:[],True:[]};total=0
for r in P:
 p=ring.Pattern(r,refined=True);dec,rs=radii_exact(p)
 if not dec:continue
 total+=1
 tup=(rs[p.out],)+tuple(sorted([rs[x] for x in p.fg]+[F(0)]*(2-len(p.fg))))
 st=p.out==(0,1)
 if any(all(a<=b for a,b in zip(tup,tt)) for tt,i in g[st]):continue
 g[st]=[(tt,i) for tt,i in g[st] if not all(a<=b for a,b in zip(tt,tup))];g[st].append((tup,r['pid']))
rs=[]
for st,ls in g.items():
 for (ro,rf,rg),pid in ls:
  c=F(961,1000) if st else F(187,200);p=ring.Pattern(P[pid],refined=True);app,ok,rad=certify_decoupled(p,c)
  rs.append(dict(straight=st,pid=pid,radii=list(map(str,[ro,rf,rg])),float_min=gram_min(float(ro),float(rf),float(rg))[0],exact_at_original=ok))
print(json.dumps(dict(patterns=total,maximal_boxes=rs),indent=2));open('data/closed_boxes.json','w').write(json.dumps(dict(patterns=total,maximal_boxes=rs),indent=2))
