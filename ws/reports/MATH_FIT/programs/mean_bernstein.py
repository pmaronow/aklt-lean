import sys,json,itertools,math,collections
from fractions import Fraction as F
sys.path.insert(0,'programs');import h1_cores as hc
import closed_exact as ce

def add(a,b):
 d=collections.defaultdict(F);d.update(a)
 for k,v in b.items():d[k]+=v
 return {k:v for k,v in d.items() if v}
def mul(a,b):
 d=collections.defaultdict(F)
 for ia,va in a.items():
  for ib,vb in b.items():d[tuple(x+y for x,y in zip(ia,ib))]+=va*vb
 return {k:v for k,v in d.items() if v}
def con(x):return {(0,0,0):F(x)}
def scale(a,x):return {k:v*x for k,v in a.items() if v*x}
def sq(a):return mul(a,a)
def linear(c,v,j):
 e=[0,0,0];e[j]=1;return {(0,0,0):c,tuple(e):v}
def poly(rs,kind):
 a,b,c=rs;R=ce.rho_exact(kind,rs)
 x=linear(a*b,-2*a*b,0);y=linear(a*c,-2*a*c,1);z=linear(b*c,-2*b*c,2)
 A=add(con(5),z);B=add(con(5),y);C=add(con(5),x)
 N=add(add(scale(sq(A),a*a),scale(sq(B),b*b)),scale(sq(C),c*c))
 for inn,aa,bb in [(x,A,B),(y,A,C),(z,B,C)]:N=add(N,scale(mul(inn,mul(aa,bb)),2))
 den=add(con(3 if kind=='u' else 5),add(x,add(y,z)))
 return add(scale(sq(den),25*R*R),scale(N,-1)),R

def bernstein(P,n):
 B={}
 for i in itertools.product(range(n+1),repeat=3):
  B[i]=sum(v*math.prod(F(math.comb(ij,kj),math.comb(n,kj)) for ij,kj in zip(i,k)) for k,v in P.items() if all(kj<=ij for ij,kj in zip(i,k)))
 return B
if __name__ == '__main__':
 calls=set();orig=hc.rho_exact

 def rho(kind,rs):
  t=tuple(sorted(list(rs)+[F(0)]*(3-len(rs))));calls.add((kind,t));return orig(kind,rs)
 hc.rho_exact=rho;ce.rho_exact=rho
 for r in hc.P:
  p=hc.ring.Pattern(r,refined=True);hc.core(p);ce.radii_exact(p)
 results=[]
 for kind,rs in sorted(calls):
  P,R=poly(rs,kind);row=dict(kind=kind,radii=list(map(str,rs)),R=str(R))
  for n in [2,3,4,6,8]:
   bs=bernstein(P,n)
   if min(bs.values())>=0:
    row.update(degree=n,coeff_count=len(bs),max_bits=max(max(abs(v.numerator).bit_length(),v.denominator.bit_length()) for v in bs.values()),minimum=str(min(bs.values())));break
  else:row['failed']=True;row['minimum_degree8']=str(min(bs.values()))
  results.append(row)
 print(json.dumps(dict(cases=len(results),failed=sum(r.get('failed',False) for r in results),results=results),indent=2))
 open('data/mean_bernstein.json','w').write(json.dumps(dict(cases=len(results),results=results),indent=2))
