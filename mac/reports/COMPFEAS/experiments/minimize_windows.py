"""Exact deterministic automaton minimization, preserving absolute step labels and kind.
No floating point. Untrusted partition intended to be rechecked from raw windows in Lean.
"""
import sys,json,time,resource
from pathlib import Path
from collections import Counter
root=Path(__file__).resolve().parents[1]
dx=[1,0,-1,0];dy=[0,1,0,-1]
def build(m):
 states=[]
 def gen(ds,x,y,used):
  if len(ds)==m:states.append(ds);return
  for d in range(4):
   a=(x,y);b=(x+dx[d],y+dy[d]);edge=tuple(sorted((a,b)))
   if edge in used:continue
   gen(ds+(d,),*b,used|{edge})
 gen((),0,0,set());codes=[sum(d*4**(m-1-i) for i,d in enumerate(ds)) for ds in states]
 lookup={c:i for i,c in enumerate(codes)};tr=[];ki=[]
 for ds in states:
  x=y=0;seen=set();used=set()
  for d in ds:
   seen.add((x,y));a=(x,y);x+=dx[d];y+=dy[d];used.add(tuple(sorted((a,(x,y)))))
  revisit=(x,y) in seen;t=[];k=[]
  for d in range(4):
   edge=tuple(sorted(((x,y),(x+dx[d],y+dy[d]))))
   if edge in used:t.append(-1);k.append(-1)
   else:
    cc=sum(dd*4**(m-1-i) for i,dd in enumerate(ds[1:]+(d,)))
    t.append(lookup[cc]);k.append(2 if revisit else 0 if d==ds[-1] else 1)
  tr.append(t);ki.append(k)
 return codes,tr,ki
for m in map(int,sys.argv[1:] or ['6','8','10']):
 start=time.monotonic();codes,tr,ki=build(m);n=len(codes)
 def classify(keys):
  ids={};out=[]
  for k in keys:
   if k not in ids:ids[k]=len(ids)
   out.append(ids[k])
  return out
 cls=classify(tuple(k) for k in ki);steps=[]
 while True:
  new=classify(tuple((ki[i][d],cls[t] if t>=0 else -1) for d,t in enumerate(ts)) for i,ts in enumerate(tr))
  steps.append(max(new)+1)
  if new==cls:break
  cls=new
 nc=max(cls)+1;reps=[None]*nc
 for i,c in enumerate(cls):
  if reps[c] is None:reps[c]=i
 # Directly recheck every transition and kind; this is the intended Lean checker.
 for i,c in enumerate(cls):
  r=reps[c]
  assert codes[i]%4==codes[r]%4 or all(k in [-1,2] for k in ki[i])
  assert ki[i]==ki[r]
  assert [(cls[t] if t>=0 else -1) for t in tr[i]]==[(cls[t] if t>=0 else -1) for t in tr[r]]
 out=root/'data'/f'windows_m{m}_min.txt'
 with out.open('w') as f:
  f.write(f'{n} {nc}\n')
  for code,c in zip(codes,cls):f.write(f'{code} {c}\n')
  for r in reps:f.write(' '.join(map(str,[codes[r]]+[cls[t] if t>=0 else -1 for t in tr[r]]+ki[r]))+'\n')
 counts=Counter(k for r in reps for k in ki[r] if k>=0)
 row=dict(m=m,raw_states=n,min_states=nc,refinement_counts=steps,edges_by_kind=dict(counts),wall=time.monotonic()-start,maxrss_bytes=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
 (root/'logs'/f'windows_m{m}_min.json').write_text(json.dumps(row,indent=2));print(json.dumps(row),flush=True)
