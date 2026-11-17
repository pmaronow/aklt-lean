import sys,json,collections,itertools
from fractions import Fraction as F
sys.path.insert(0,'/home/ubuntu/aklt/compfeas/programs/h1-local/code')
import ring
from closed_exact import rho_exact
P=json.load(open('/home/ubuntu/aklt/compfeas/programs/data/pext/pext7962.json'))

def core(p):
 adj={x:set() for x in ring.RING}
 for i in range(8):
  if p.ringbond[i]:
   x,y=ring.RING[i],ring.RING[(i+1)%8];adj[x].add(y);adj[y].add(x)
 alive=set(p.vn);todo=list(p.vn)
 while todo:
  for y in adj[todo.pop()]:
   if y not in alive:alive.add(y);todo.append(y)
 fs={x:([ring.TIPRAD] if x in ring.TIP and ring.bk(x,ring.TIP[x]) in p.present else [])+([F(1)]*p.nslot[x] if x not in ring.TIP else []) for x in alive}
 change=True
 while change:
  change=False
  for x in list(alive):
   if x in p.vn:continue
   n=adj[x]&alive
   if len(n)<2:
    alive.remove(x);change=True
    if n:
     y=next(iter(n));r=rho_exact(p.kind[x],fs[x])
     if r:fs[y].append(r)
 # canonical component paths / cycles; retain coordinates only in witness
 comps=[];seen=set()
 for x in alive:
  if x in seen:continue
  cc={x};stack=[x]
  while stack:
   for y in adj[stack.pop()]&alive:
    if y not in cc:cc.add(y);stack.append(y)
  seen|=cc
  ends=[x for x in cc if len(adj[x]&alive)<2];cycle=not ends
  starts=cc if cycle else ends
  enc=[]
  for a in starts:
   for b in ([None] if len(cc)==1 else adj[a]&alive):
    path=[a];prev=None;cur=a;nxt=b
    while nxt is not None and nxt!=a:
     path.append(nxt);prev,cur=cur,nxt
     ns=(adj[cur]&alive)-{prev};nxt=next(iter(ns)) if ns else None
    def attr(x,withrad):
     base=(p.kind[x],int(x in p.vn),int(x==p.out))
     return base+(tuple(sorted(fs[x])) if withrad else len(fs[x]),)
    attrs=tuple(attr(x,True) for x in path)
    geom=tuple(attr(x,False) for x in path)
    enc.append((geom,attrs,tuple(path)))
  comps.append((int(cycle),min(enc)))
 comps.sort(key=lambda a:(a[0],a[1][:2]));
 key=tuple((cyc,gg) for cyc,(gg,attrs,path) in comps)
 attrs=tuple(attrs for cyc,(gg,attrs,path) in comps)
 paths=tuple(path for cyc,(gg,attrs,path) in comps)
 return key,attrs,paths,fs

def dominates(a,b):return all(all(all(x<=y for x,y in zip(ra[-1],rb[-1])) for ra,rb in zip(ca,cb)) for ca,cb in zip(a,b))

if __name__=='__main__':
 for ref in [False,True]:
  g=collections.defaultdict(list)
  for r in P:
   p=ring.Pattern(r,refined=ref);key,attrs,paths,fs=core(p)
   if all(len(c[1])==1 for c in key):continue
   g[(tuple(p.out)==(0,1),key)].append((attrs,r['pid'],paths))
  maximal=[]
  for (straight,key),rs in g.items():
   keep=[]
   for a,pid,paths in rs:
    if any(dominates(a,b) for b,i,pa in keep):continue
    keep=[(b,i,pa) for b,i,pa in keep if not dominates(b,a)];keep.append((a,pid,paths))
   maximal += [dict(straight=straight,key=key,attrs=a,pid=pid,paths=paths) for a,pid,paths in keep]
  def conv(o):
   if isinstance(o,F):return str(o)
   raise TypeError
  open('data/cores_'+str(ref)+'.json','w').write(json.dumps(maximal,default=conv))
  print(ref,'geometries',len(g),'maximal',len(maximal),'slotcounts',collections.Counter(sum(len(a[-1]) for comp in r['attrs'] for a in comp) for r in maximal))
