import sys,json,collections,copy,itertools
from fractions import Fraction as F
sys.path.insert(0,'programs');from h1_cores import core,dominates,P,ring
mode=sys.argv[1] if len(sys.argv)>1 else 'count'
g=collections.defaultdict(list)
for r in P:
 p=ring.Pattern(r,refined=True)
 # Every D with degree<=2 total (internal+actual external slots) is .6*U+.4*delta0.
 # Enumerate its two alternatives: delta0 deletes the vertex and all its bonds.
 ds=[x for x in p.kind if p.kind[x]=='d']
 for bits in itertools.product([0,1],repeat=len(ds)):
  a=copy.copy(p);a.kind=dict(p.kind);a.present=set(p.present);a.nslot=dict(p.nslot)
  for x,bit in zip(ds,bits):
   a.kind[x]='u'
   if not bit:
    a.present={b for b in a.present if x not in b};a.nslot[x]=0
  a.vn=[x for x in (ring.E,ring.N,ring.W) if ring.bk(ring.V,x) in a.present]
  if a.out not in a.vn:
   # out deleted: Znext and Zcur have no out interaction, but fg term remains;
   # this is still a nontrivial scalar F=(1-c)Z+(1/3-c/5)Cfg.
   pass
  a.ringbond=[ring.bk(ring.RING[i],ring.RING[(i+1)%8]) in a.present for i in range(8)]
  a.live={x:any(x in b for b in a.present) for x in ring.RING}
  key,attrs,paths,fs=core(a)
  if not a.vn:continue
  g[(tuple(p.out)==(0,1),key)].append((attrs,r['pid'],paths,bits))
maximal=[]
for (straight,key),rs in g.items():
 keep=[]
 for a,pid,paths,bits in rs:
  if any(dominates(a,b) for b,i,pa,bb in keep):continue
  keep=[(b,i,pa,bb) for b,i,pa,bb in keep if not dominates(b,a)]
  keep.append((a,pid,paths,bits))
 maximal += [dict(straight=straight,key=key,attrs=a,pid=pid,paths=paths,bits=bits) for a,pid,paths,bits in keep]
print('allU mixture geometries',len(g),'maximal',len(maximal),'slotcounts',collections.Counter(sum(len(a[-1]) for comp in r['attrs'] for a in comp) for r in maximal),flush=True)
def conv(o):
 if isinstance(o,F):return str(o)
 raise TypeError
open('data/cores_convex.json','w').write(json.dumps(maximal,default=conv))
