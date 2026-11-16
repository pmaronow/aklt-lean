"""Exact integer Collatz checks, with windows generated from bond-trail definitions.
Untrusted floating candidates are averaged on D4 orbits then rounded to integers.
"""
import sys,json,time,math,resource
from pathlib import Path
from fractions import Fraction as F
root=Path(__file__).resolve().parents[1]
m=int(sys.argv[1]);k=int(sys.argv[2]);rev=F(sys.argv[3]);vfile=root/sys.argv[4]
DX=[1,0,-1,0];DY=[0,1,0,-1]
def bond(x,y,d):
 a=(x,y);b=(x+DX[d],y+DY[d]);return (a,b) if a<b else (b,a)
def encode(ds):return sum(d*4**i for i,d in enumerate(ds))
def decode(c):return tuple((c//4**i)%4 for i in range(m))
def canon(ds):
 return min(encode(tuple((sgn*d+r)%4 for d in ds)) for sgn in [1,-1] for r in range(4))
def generate(left,x,y,ds,used):
 if left==0:yield ds;return
 for d in range(4):
  b=bond(x,y,d)
  if b in used:continue
  yield from generate(left-1,x+DX[d],y+DY[d],ds+(d,),used|{b})
start=time.monotonic();windows=list(generate(m,0,0,(),set()));orb={encode(ds):canon(ds) for ds in windows}
cl=sorted(set(orb.values()));vf={int(a):float(b) for a,b in (l.split() for l in open(vfile))}
scale=10**12
members={c:[] for c in cl}
for code,c in orb.items():members[c].append(vf[code])
# min=max/100 is the paper's M8 witness condition; retain it also in smaller tests.
H={c:max(scale//100,round(scale*sum(v)/len(v))) for c,v in members.items()}
weights=[F(1000,2883),F(200,561),rev]
D=math.lcm(*(a.denominator for a in weights));nums=[int(D*a) for a in weights]
nodes=[0]*(k+1);products=0;leaf=0;rows=[];best=F(0)
def ext(left,x,y,last,dirs,used,depart,w):
 global products,leaf
 nodes[k-left]+=1
 if left==0:
  leaf+=1
  return w*H[orb[encode(dirs[-m:])]]
 total=0
 for d in range(4):
  b=bond(x,y,d)
  if b in used:continue
  ty=2 if depart.get((x,y),0) else (0 if d==last else 1)
  depart[(x,y)]=depart.get((x,y),0)+1
  used.add(b);dirs.append(d);products+=1
  total+=ext(left-1,x+DX[d],y+DY[d],d,dirs,used,depart,w*nums[ty])
  dirs.pop();used.remove(b);depart[(x,y)]-=1
 return total
for j,c in enumerate(cl):
 ds=decode(c);x=y=0;used=set();depart={}
 for d in ds:
  used.add(bond(x,y,d));depart[(x,y)]=depart.get((x,y),0)+1;x+=DX[d];y+=DY[d]
 val=ext(k,x,y,ds[-1],list(ds),used,depart,1)
 ratio=F(val,D**k*H[c]);best=max(best,ratio)
 rows.append(dict(code=c,h=H[c],sum=val,den=D**k,orbit_size=len(members[c])))
 if j%100==0:print(j,len(cl),'wall',time.monotonic()-start,flush=True)
qtarget=F('0.98075') if (m,k,rev)==(8,8,F(1,4)) else F('0.9996') if (m,k,rev)==(6,1,F(1,5)) else F('0.9999')
ok=best<=qtarget**k
result=dict(m=m,k=k,revisit=str(rev),windows=len(windows),classes=len(cl),D=D,nums=nums,nodes=nodes,weight_mults=products,leaves=leaf,max_ratio=str(best),max_ratio_float=float(best),qtarget=str(qtarget),ok=ok,wall=time.monotonic()-start,maxrss_bytes=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,max_sum_bits=max(r['sum'].bit_length() for r in rows),h_ratio=str(F(max(H.values()),min(H.values()))))
(root/'data'/f'h2_exact_m{m}k{k}_r{rev.denominator}.json').write_text(json.dumps(dict(summary=result,rows=rows),indent=2))
(root/'logs'/f'h2_exact_m{m}k{k}_r{rev.denominator}_summary.json').write_text(json.dumps(result,indent=2))
print(json.dumps(result,indent=2))
