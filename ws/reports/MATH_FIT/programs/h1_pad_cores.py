import sys,json,collections,itertools,copy
from fractions import Fraction as F
sys.path.insert(0,'programs');import h1_cores as hc
# Re-canonicalize after adding zero-radius factors, and collapse isolated marked vertices to their means.
def canon(desc):
 comps=[]
 for (cycle,geom),attrs,path in zip(desc['key'],desc['attrs'],desc['paths']):
  attrs=[list(a) for a in attrs];path=[tuple(x) for x in path]
  if len(attrs)==1:
   k,iv,io,rs=attrs[0];assert iv
   rr=hc.rho_exact(k,[F(r) for r in rs]);attrs=[['m',iv,io,[rr]]]
  else:
   for j,a in enumerate(attrs):
    k,iv,io,rs=a;rs=[F(r) for r in rs]
    deg=2 if cycle or j not in [0,len(attrs)-1] else 1
    nn=(4 if k=='u' else 2)-iv-deg
    assert nn>=len(rs),(a,deg,nn)
    a[3]=[F(0)]*(nn-len(rs))+sorted(rs)
  alts=[]
  if cycle:
   for t in range(len(attrs)):
    for sg in [1,-1]:
     js=[(t+sg*j)%len(attrs) for j in range(len(attrs))];al=[tuple(attrs[j][:3])+(tuple(attrs[j][3]),) for j in js];pa=[path[j] for j in js];ge=tuple(a[:3]+(len(a[3]),) for a in al);alts.append((ge,tuple(al),tuple(pa)))
  else:
   for js in [list(range(len(attrs))),list(reversed(range(len(attrs))))]:
    al=[tuple(attrs[j][:3])+(tuple(attrs[j][3]),) for j in js];pa=[path[j] for j in js];ge=tuple(a[:3]+(len(a[3]),) for a in al);alts.append((ge,tuple(al),tuple(pa)))
  comps.append((cycle,min(alts)))
 comps.sort(key=lambda x:x[1][:2])
 return tuple((c,g) for c,(g,a,p) in comps),tuple(a for c,(g,a,p) in comps),tuple(p for c,(g,a,p) in comps)
g=collections.defaultdict(list)
for r in hc.P:
 p=hc.ring.Pattern(r,refined=True);key,attrs,paths,fs=hc.core(p)
 if all(len(comp[1])==1 for comp in key):continue
 de=dict(key=key,attrs=attrs,paths=paths);key,attrs,paths=canon(de);g[(p.out==(0,1),key)].append((attrs,r['pid'],paths))
maximal=[]
for (st,key),rows in g.items():
 keep=[]
 for a,pid,paths in rows:
  if any(hc.dominates(a,b) for b,i,pa in keep):continue
  keep=[(b,i,pa) for b,i,pa in keep if not hc.dominates(b,a)];keep.append((a,pid,paths))
 maximal.extend(dict(straight=st,key=key,attrs=a,pid=pid,paths=pa) for a,pid,pa in keep)
def conv(o):
 if isinstance(o,F):return str(o)
 raise TypeError
open('data/cores_padded.json','w').write(json.dumps(maximal,default=conv))
print('geometries',len(g),'maxima',len(maximal),'slots',dict(collections.Counter(sum(sum(r!=0 for r in a[3]) for comp in d['attrs'] for a in comp) for d in maximal)))
