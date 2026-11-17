import sys,json,collections,math,ast
from pathlib import Path
sys.path.insert(0,'/home/ubuntu/aklt/compfeas/programs/h1-local/code')
import ring
from collapse import Tree
from closed_exact import radii_exact
from fractions import Fraction as F
P=json.load(open('/home/ubuntu/aklt/compfeas/programs/data/pext/pext7962.json'))
for refined in [False,True]:
 groups=collections.defaultdict(list); counts=collections.Counter(); total=[0,0,0]
 for r in P:
  p=ring.Pattern(r,refined=refined);t=Tree(p)
  if t.decoupled():counts['decoupled']+=1;continue
  core=[]
  for x in ring.RING:
   if x in t.alive:core.append((x,p.kind[x],tuple(sorted(tuple(sorted(e)) for e in t.edges if x in e)),tuple(t.fields[x])))
  sig=(p.out,tuple(core));groups[sig].append(r['pid'])
  n=sum(len(fs) for fs in t.fields.values())
  counts[('slots',n)]+=1
 print('REFINED',refined,'counts',dict(counts),'groups',len(groups),'largest classes', sorted([len(g) for g in groups.values()],reverse=True)[:10])
 # same topology and local kind, independent fields ordered by radii; fields attached at each node commute.
 coregroups=collections.defaultdict(list)
 for sig,pids in groups.items():
  out,core=sig
  key=(out,tuple((x,k,e,len(fs)) for x,k,e,fs in core))
  fields=tuple(sorted(fs) for x,k,e,fs in core)
  coregroups[key].append((fields,pids))
 print('core geometry/kind/field-number groups',len(coregroups))
 maxima=[]
 for key,rs in coregroups.items():
  # Count non-dominated field boxes
  keep=[]
  for fs,pids in rs:
   def le(a,b):return all(all(x<=y+1e-14 for x,y in zip(f,g)) for f,g in zip(a,b))
   if any(le(fs,gg) for gg,ii in keep):continue
   keep=[(gg,ii) for gg,ii in keep if not le(gg,fs)]
   keep.append((fs,pids))
  maxima.extend((key,fs,pids) for fs,pids in keep)
 print('maximal boundary boxes',len(maxima))
 print('largest slots',collections.Counter(sum(k[3] for k in key[1]) for key,fs,pids in maxima))
 out=[dict(key=key,radii=fs,pids=pids) for key,fs,pids in maxima]
 Path('data/h1_maximal_'+str(refined)+'.json').write_text(json.dumps(out))
