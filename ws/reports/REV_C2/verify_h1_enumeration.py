import itertools,json,time,resource,ast
from pathlib import Path
root=Path('/home/ubuntu/aklt/compfeas')
h1_output_root=Path('/home/ubuntu/aklt/reports/REV_C2/checks')
V=(0,0);S=(0,-1);E=(1,0);N=(0,1);W=(-1,0)
d1=[E,N,W,S];corners=[(1,1),(-1,1),(-1,-1),(1,-1)];dirs=[(1,0),(0,1),(-1,0),(0,-1)]
def nbr(x,d):return (x[0]+dirs[d][0],x[1]+dirs[d][1])
def bond(a,b):return tuple(sorted((a,b)))
def options(x):
 if x in corners:return [('u',15),('x',0)]+[('d',sum(1<<d for d in ds)) for ds in itertools.combinations(range(4),2)]
 toV=next(d for d in range(4) if nbr(x,d)==V)
 if x==S:
  return [('x',0)]+[('d',sum(1<<d for d in ds)) for ds in itertools.combinations([d for d in range(4) if d!=toV],2)]
 return [('u',15),('x',0)]+[('d',(1<<toV)|(1<<d)) for d in range(4) if d!=toV]
def canon(kind,present,out):
 keys=[]
 for sign in [1,-1]:
  f=lambda x:(sign*x[0],x[1])
  keys.append((f(out),tuple(sorted((f(x),k) for x,k in kind.items())),tuple(sorted(bond(f(a),f(b)) for a,b in present))))
 return min(keys)
P=json.load(open(root/'programs/data/pext/pext7962.json'))
keys={canon({ast.literal_eval(x):k for x,k in r['kinds'].items()},[(tuple(a),tuple(b)) for a,b in r['present']],tuple(r['out'])):r['pid'] for r in P}
start=time.monotonic();reps=set();nvalid=0;nout=0;outcounts={str(x):0 for x in [E,N,W]};checks=0;raw=0
ops1=[options(x) for x in d1];opsc=[options(x) for x in corners]
for combo in itertools.product(*ops1):
 ch=dict(zip(d1,combo))
 allowed=[]
 for c,opts in zip(corners,opsc):
  good=[]
  for typ,mask in opts:
   valid=True
   for d in range(4):
    x=nbr(c,d)
    if x in ch:
     xt,xm=ch[x];dd=next(j for j in range(4) if nbr(x,j)==c);checks+=1
     if typ!='x' and xt!='x' and bool(mask&(1<<d))!=bool(xm&(1<<dd)):valid=False;break
   if valid:good.append((typ,mask))
  allowed.append(good)
 for cornercombo in itertools.product(*allowed):
  raw+=1;ch.update(zip(corners,cornercombo));present=set()
  for x in d1:
   typ,mask=ch[x]
   if typ=='x':continue
   for d in range(4):
    if not mask&(1<<d):continue
    y=nbr(x,d)
    if y==V:
     if x!=S:present.add(bond(x,y))
    elif y not in ch:present.add(bond(x,y))
    else:
     yt,ym=ch[y];dd=next(j for j in range(4) if nbr(y,j)==x)
     if yt!='x' and ym&(1<<dd):present.add(bond(x,y))
  relevant={z for b in present for z in b};kind={x:typ for x,(typ,mask) in ch.items() if x in relevant}
  for out in [N,E,W]:
   if bond(V,out) not in present:continue
   nvalid+=1;outcounts[str(out)]+=1
   if out==W:continue
   nout+=1;key=canon(kind,present,out);assert key in keys;reps.add(key)
result=dict(valid_status_configurations=raw,valid_out_marked_all=nvalid,valid_out_marked_N_E=nout,out_counts=outcounts,classes=len(reps),missing=len(set(keys)-reps),consistency_tests=checks,wall=time.monotonic()-start,maxrss_bytes=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
(h1_output_root/'h1_enumeration.json').write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2))
