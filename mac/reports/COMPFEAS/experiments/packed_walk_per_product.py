"""Prototype fixed-point, bit-packed memory walk; inputs are numerical C prefix enclosures.
Does not claim a Lean proof. All DP arithmetic after import is exact Python Nat arithmetic.
"""
import sys,os,json,time,array,struct,math,resource
from pathlib import Path
from fractions import Fraction as F
root=Path(__file__).resolve().parents[1]
m,L,K,T,AT=map(int,sys.argv[1:6]);X=sys.argv[6];D0=int(sys.argv[7]);name=sys.argv[8]
width=160;prec=64;wprec=48;limit=96
B=1<<width;Q=2*K*K;N=width*Q;Bmod=1<<N;allmask=Bmod-1
ones=allmask//(B-1);lowmask=ones*((1<<(width-wprec))-1);highmask=ones*((B-1)^((1<<limit)-1));roundmask=ones*((1<<wprec)-1)
raw=Path(root/'data'/f'windows_m{m}_min.txt').read_text().splitlines();nraw,nw=map(int,raw[0].split());state=[list(map(int,l.split())) for l in raw[nraw+1:]]
codes=[s[0] for s in state];tr=[s[1:5] for s in state];ki=[s[5:9] for s in state]
counts=dict(mul_up=0,permutes=0,nat_mul=0,nat_add=0,nat_shift=0,nat_land=0,nat_lor=0,bound_checks=0,edge_visits=0)
start=time.monotonic()
def idx(x,y):
 p=(x+y)%(2*K);q=(x-y)%(2*K);return p*K+(q-(p&1))//2
csite=idx(0,0);usite=idx(-1,0);vsite=idx(1,0) if X=='B' else idx(0,1)
dx=[1,0,-1,0];dy=[0,1,0,-1]
id0=idx(-1+dx[D0],dy[D0]) if D0>=0 else -1
special={usite}|({id0} if D0>=0 else set())
# Full field masks, not masks of one chosen field bit.
def fields(indices):return sum((B-1)<<(width*i) for i in indices)
even=fields(i for i in range(Q) if (i//K)%2==0);odd=allmask^even
first=fields(range(0,Q,K));last=fields(range(K-1,Q,K));nfirst=allmask^first;nlast=allmask^last
regular=allmask^fields(special);killmask=allmask^fields([csite,vsite])
def colshift(a,d):
 counts['nat_land']+=2;counts['nat_shift']+=2;counts['nat_lor']+=1
 if d==1:return ((a&nlast)<<width)|((a&last)>>(width*(K-1)))
 return ((a&nfirst)>>width)|((a&first)<<(width*(K-1)))
def permute(a,d):
 counts['permutes']+=1;counts['nat_land']+=2;counts['nat_lor']+=2;counts['nat_shift']+=2
 if d in [0,3]:a=(a&even)|colshift(a&odd,1)
 else:a=(a&odd)|colshift(a&even,-1)
 shift=width*K
 if d in [0,1]:return ((a<<shift)&allmask)|(a>>(N-shift))
 return (a>>shift)|((a&((1<<shift)-1))<<(N-shift))
def mult(a,n):
 counts['mul_up']+=1;counts['nat_mul']+=1;counts['nat_add']+=1;counts['nat_shift']+=1;counts['nat_land']+=1
 return ((a*n+roundmask)>>wprec)&lowmask
# Weights are exact rationals rounded upward once to a fixed dyadic grid.
xs=F(1000,961);xt=F(200,187);h=F(6,5)
ca=[F(145217,10**6),F(150000,10**6)];cb=[F(352782,10**6),F(357549,10**6)];bp=[F(340008,10**6),F(344661,10**6)]
def coeff(q):return (q.numerator*(1<<wprec)+q.denominator-1)//q.denominator
fifth=coeff(F(1,5));third=coeff(F(1,3));fs=coeff(xs/3);ft=coeff(xt/3)
def kappa(ain,d,deadloc=None):
 back=(ain+2)%4;others=[j for j in range(4) if j!=back and j!=d];f,g=others;out=d
 def pair(a,b):return F(1) if dx[a]==dx[b] or dy[a]==dy[b] else h
 ty=0 if d==ain else 1
 df=deadloc==f;dg=deadloc==g
 if df and dg:return F(0)
 if df:return bp[ty]*pair(g,out)
 if dg:return bp[ty]*pair(f,out)
 return ca[ty]*pair(f,g)+cb[ty]*(pair(f,out)+pair(g,out))
# Prefix file: C-produced binary32 enclosure. This import is for prototype comparison only.
cache=root/'data/prefix'/f'packed_{name}.bin'
with open(cache,'rb') as f:
 hdr=struct.unpack('qqq',f.read(24));assert hdr==(nw,Q,L),hdr
 closed=list(struct.unpack('256d',f.read(256*8)))
 V=[]
 for p in range(4):
  ar=array.array('f');ar.fromfile(f,nw*Q);pv=[]
  for w in range(nw):
   out=bytearray()
   for v in ar[w*Q:(w+1)*Q]:
    a,b=v.as_integer_ratio();x=(a*(1<<prec)+b-1)//b;assert x<1<<limit;out+=x.to_bytes(width//8,'little')
   pv.append(int.from_bytes(out,'little'))
  V.append(pv)
cache.unlink()
# Independently check the packed site permutation at every site before using it.
for d in range(4):
 test=sum((i+1)<<(width*i) for i in range(Q));out=permute(test,d)
 for s in range(Q):
  p=s//K;r=s%K;q=2*r+(p&1);x=(p+q)//2;y=(p-q)//2
  t=idx(x+dx[d],y+dy[d]);assert (out>>(width*t))&(B-1)==s+1
# R2 response split masks. For a neighboring source at -direction e, c is in direction e.
near=[(idx(-dx[e],-dy[e]),e) for e in range(4)]
response_masks={}
for ain in range(4):
 for d in range(4):
  if d==(ain+2)%4:
   response_masks[ain,d]=[];continue
  groups={}
  for s,e in near:groups.setdefault(kappa(ain,d,e),[]).append(s)
  groups.setdefault(kappa(ain,d),[])
  covered=fields([s for s,e in near]);masks=[]
  for kap,ss in groups.items():
   mm=fields(ss)
   if kap==kappa(ain,d):mm|=allmask^covered
   masks.append((mm&regular,coeff((xs if d==ain else xt)*kap/3)))
  response_masks[ain,d]=masks
rows=[]
for t in range(L,T):
 exact=t+1<=AT;Nv=[[0]*nw for p in range(4)]
 for w in range(nw):
  ain=codes[w]&3
  for d,target in enumerate(tr[w]):
   if target<0:continue
   counts['edge_visits']+=1;k=ki[w][d]
   src=[V[p][w] for p in range(4)]
   if exact:
    reg=[a&regular for a in src];counts['nat_land']+=4
   else:reg=src
   diag=[fifth]*4 if k==2 else [fs,fs,fs,third] if k==0 else [ft,third,third,third]
   v=[mult(a,c) for a,c in zip(reg,diag)]
   if k!=2:
    psrc,pdst=(1,3) if k==0 else (0,2)
    masks=response_masks[ain,d] if exact else [(allmask,coeff((xs if k==0 else xt)*kappa(ain,d)/3))]
    for mask,c in masks:
     if c:
      v[pdst]+=mult(src[psrc]&mask,c);counts['nat_land']+=1;counts['nat_add']+=1
   if exact:
    for s in special:
     # Safe for L >= m+2; see report. A third visit is impossible in a true trail.
     assert L>=m+2
     if k==2:continue
     if D0>=0 and ((s==usite and d==D0) or (s==id0 and d==(D0+2)%4)):continue
     field=(B-1)<<(width*s)
     for p in range(4):v[p]+=mult(src[p]&field,fifth);counts['nat_land']+=1;counts['nat_add']+=1
   for p in range(4):Nv[p][target]+=permute(v[p],d);counts['nat_add']+=1
 V=Nv
 for p in range(4):
  for w in range(nw):
   counts['bound_checks']+=1;counts['nat_land']+=1
   if V[p][w]&highmask:raise OverflowError((t,p,w))
 arr=sum(((V[2][w]>>(width*vsite))&(B-1))+((V[3][w]>>(width*vsite))&(B-1)) for w in range(nw))
 rows.append((t+1,str(F(arr,1<<prec))))
 if exact:
  for p in range(4):
   V[p]=[a&killmask for a in V[p]];counts['nat_land']+=nw
 if (t+1)%10==0:print('step',t+1,'arrival',float(F(arr,1<<prec)),'wall',time.monotonic()-start,flush=True)
result=dict(m=m,L=L,K=K,T=T,AT=AT,X=X,D0=D0,nw=nw,sites=Q,storage_bits=width,scale_bits=prec,weight_bits=wprec,plane_bits=N,counts=counts,wall=time.monotonic()-start,maxrss_bytes=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,arrivals=rows,closed=closed[:L+1])
(root/'logs'/f'packed_{name}.json').write_text(json.dumps(result,indent=2));print(json.dumps({k:v for k,v in result.items() if k not in ['arrivals','closed']},indent=2))
