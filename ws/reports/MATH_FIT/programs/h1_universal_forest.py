import sys,json,itertools,collections
from fractions import Fraction as F
sys.path.insert(0,'programs');import h1_cores as hc
# h1_pad_cores currently executes its enumeration when imported; keep its canonicalizer in a separate namespace.
s=open('programs/h1_pad_cores.py').read();s=s[:s.index('\ng=collections.defaultdict(list)')];ns={};exec(s,ns);canon=ns['canon']
R=hc.ring;U=[R.E,R.N,R.W];top=[R.C0,R.C1];bottom={R.E:R.C3,R.W:R.C2};g=collections.defaultdict(list);nterms=0;nclosed=0
for rec in hc.P:
 p=R.Pattern(rec,refined=True);ds=[x for x in p.vn if p.kind[x]=='d'];dc=[c for c in top if p.kind.get(c)=='d' and sum(R.bk(c,x) in p.present for x in U)==2]
 for bits in itertools.product([0,1],repeat=len(ds)+len(dc)):
  alive=set(p.vn)-{x for x,b in zip(ds,bits) if not b};activecorner={c for c,b in zip(dc,bits[len(ds):]) if b};nterms+=1
  pp=object.__new__(R.Pattern);pp.out=p.out;pp.vn=[x for x in U if x in alive];pp.kind={x:'u' for x in R.RING};pp.ringbond=[False]*8;pp.live={x:x in alive for x in R.RING};pp.present=set();pp.nslot={x:0 for x in R.RING}
  fields={x:[] for x in alive};bridges=[]
  for x in alive:
   if R.bk(x,R.TIP[x]) in p.present:fields[x].append(F(3,5))
   if x in bottom and R.bk(x,bottom[x]) in p.present:fields[x].append(F(3,5))
  for c in top:
   oldnb=[x for x in U if R.bk(c,x) in p.present];nb=[x for x in oldnb if x in alive];k=p.kind.get(c)
   if k=='u':
    if len(nb)==2:bridges.append((c,nb))
    elif len(nb)==1:fields[nb[0]].append(F(1,2))
   elif k=='d':
    if len(oldnb)==2:
     if c in activecorner and len(nb)==2:bridges.append((c,nb))
    elif len(nb)==1:fields[nb[0]].append(F(1,5))
  for c,nb in bridges:
   pp.live[c]=True;pp.nslot[c]=2
   for x in nb:pp.present.add(R.bk(c,x))
  for x in alive:pp.present.add(R.bk(R.V,x))
  pp.ringbond=[R.bk(R.RING[i],R.RING[(i+1)%8]) in pp.present for i in range(8)]
  # Build descriptors directly, because the contracted E/W fields need not be literal tip slots.
  adj={x:set() for x in R.RING}
  for c,nb in bridges:
   for x in nb:adj[x].add(c);adj[c].add(x)
  seen=set();comps=[]
  for x in alive:
   if x in seen:continue
   cc={x};stack=[x]
   while stack:
    for y in adj[stack.pop()]:
     if y not in cc:cc.add(y);stack.append(y)
   seen|=cc;start=next(y for y in cc if len(adj[y])<2);path=[start];prev=None;cur=start
   while True:
    nx=adj[cur]-({prev} if prev is not None else set())
    if not nx:break
    nxt=next(iter(nx));path.append(nxt);prev,cur=cur,nxt
   attrs=[['u',int(x in alive),int(x==p.out),fields[x] if x in alive else [F(1),F(1)]] for x in path]
   comps.append((path,attrs))
  if not comps:continue
  de=dict(key=[[0,[]] for pa,aa in comps],attrs=[aa for pa,aa in comps],paths=[pa for pa,aa in comps]);key,attrs,paths=canon(de)
  g[(p.out==(0,1),key)].append((attrs,rec['pid'],paths))
maximal=[]
for (st,key),rows in g.items():
 keep=[]
 for a,pid,pa in rows:
  if any(hc.dominates(a,b) for b,i,pp in keep):continue
  keep=[(b,i,pp) for b,i,pp in keep if not hc.dominates(b,a)];keep.append((a,pid,pa))
 maximal.extend(dict(straight=st,key=key,attrs=a,pid=pid,paths=pa) for a,pid,pa in keep)
def conv(o):
 if isinstance(o,F):return str(o)
 raise TypeError
open('data/cores_universal.json','w').write(json.dumps(maximal,default=conv))
print('terms',nterms,'geometries',len(g),'maximal',len(maximal),'slots',dict(collections.Counter(sum(sum(r!=0 for r in a[3]) for comp in d['attrs'] for a in comp) for d in maximal)))
