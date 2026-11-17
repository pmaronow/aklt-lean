import sys,types,math,itertools,json,copy,time
from fractions import Fraction as F
import numpy as np
sys.path.insert(0,'/home/ubuntu/aklt/compfeas/programs/h1-local/code')
import ring,cert
R=ring.RING
class CorePattern(ring.Pattern):
 def __init__(self,desc):
  self.desc=desc;self.live={x:False for x in R};self.kind={x:'u' for x in R};self.vn=[];self.out=(999,999);self.ringbond=[False]*8;self.vars=[];self.radii=[];self.nslot={x:0 for x in R}
  edges=set();self.fields={}
  for (cycle,geom),attrs,path in zip(desc['key'],desc['attrs'],desc['paths']):
   path=[tuple(x) for x in path]
   for x,a in zip(path,attrs):
    k,iv,io,rs=a;self.kind[x]=k;self.live[x]=True
    if iv:self.vn.append(x)
    if io:self.out=x
    self.fields[x]=[F(r) for r in rs]
    self.vars.extend([(x,'custom')]*len(rs));self.radii.extend(self.fields[x]);self.nslot[x]=len(rs)
   for x,y in zip(path,path[1:]):edges.add(ring.bk(x,y))
   if cycle:edges.add(ring.bk(path[-1],path[0]))
  self.fg=[x for x in self.vn if x!=self.out];self.nv=len(self.vars);self.rad=np.array(list(map(float,self.radii)))
  for i in range(8):self.ringbond[i]=ring.bk(R[i],R[(i+1)%8]) in edges
 def site_weights(self,U):
  om={x:self.base(x) for x in R}
  for (x,t),rad,u in zip(self.vars,self.rad,U):om[x]*=1+rad*(ring.FR@u)
  return om
class CoreNet(cert.Net):
 def __init__(self,p):
  self.p=p;self.T={};self.scale=1;self.site_slots={x:[] for x in R};self.slots=[]
  for i,x in enumerate(R):
   fs=p.fields.get(x,[]);ns=len(fs);self.site_slots[x]=list(range(len(self.slots),len(self.slots)+ns));self.slots.extend([(x,'custom')]*ns)
   L=p.ringbond[i-1];RR=p.ringbond[i];vleg=x in p.vn
   if not p.live[x]:self.T[x]=np.ones((1,1,1),dtype=object);continue
   k=int(L)+int(RR)+int(vleg)+ns;M,lcd=cert.mtensor(k,p.kind[x]);M=np.rint(M).astype(object);M=M.reshape([4 if L else 1,4 if RR else 1,4 if vleg else 1]+[4]*ns)
   self.scale*=lcd
   for j,r in enumerate(fs):
    sh=[1]*M.ndim;sh[3+j]=4;M=M*np.array([r.denominator,r.numerator,r.numerator,r.numerator],dtype=object).reshape(sh);self.scale*=r.denominator
   self.T[x]=M
  self.n=len(self.slots)
 def half(self,sites,vidx):
  A=None
  for x in sites:
   t=self.T[x];a=vidx.get(x,0);t=t[:,:,a] if t.shape[2]>1 else t[:,:,0]
   if A is None:A=t
   else:
    A=np.tensordot(A,t,axes=([1],[0]));nA=A.ndim-t.ndim+1;A=np.moveaxis(A,nA,1)
  return A
 def ring(self,vidx):
  h1=self.half(R[:4],vidx);h2=self.half(R[4:],vidx);s1=h1.shape[2:];s2=h2.shape[2:]
  a=h1.reshape(h1.shape[0],h1.shape[1],-1);b=h2.reshape(h2.shape[0],h2.shape[1],-1)
  return np.tensordot(a,b,axes=([0,1],[1,0])).reshape(s1+s2)
 def cur_next_int(self):
  Z=self.ring({});C={}
  for x,y in [(ring.E,ring.N),(ring.E,ring.W),(ring.N,ring.W)]:
   if x in self.p.vn and y in self.p.vn:C[frozenset((x,y))]=sum(self.ring({x:k,y:k}) for k in [1,2,3])
  return 3*Z+sum(C.values()),5*Z+(C[frozenset(self.p.fg)] if len(self.p.fg)==2 else 0)
class CoreCertificate:
 def __init__(self,desc):
  self.p=CorePattern(desc);self.net=CoreNet(self.p);self.cur,self.nxt=self.net.cur_next_int();self.n=self.net.n
  # Only two unit slots at a U site share a supported spin-1 representation.
  self.opnet=types.SimpleNamespace(n=self.n,site_slots={x:[] for x in R},slots=[],p=types.SimpleNamespace(kind={x:'u' for x in R}))
  G=[]
  for x in R:
   ids=self.net.site_slots[x];rs=self.p.fields.get(x,[])
   if len(ids)==2 and self.p.kind[x]=='u' and all(r==1 for r in rs):G.append(ids)
   else:G.extend([[i] for i in ids])
  assert len(G)<=8
  for x,g in zip(R,G):self.opnet.site_slots[x]=g;self.opnet.slots.extend([(x,'custom')]*len(g))
  # operator_sym expects f.dtype int64. Its integer algorithm supports object arrays after this check.
  self.G=G
 def ops(self,S):
  return operator(self.opnet,self.cur,S),operator(self.opnet,self.nxt,S)
 def c_S(self,S):
  (A,q,fa),(B,q2,fb)=self.ops(S);best=math.inf;dims=[]
  for sec in cert.sector_list(q,True):
   ix=np.where(q==sec)[0];dims.append(len(ix));a=A[np.ix_(ix,ix)].astype(float);b=B[np.ix_(ix,ix)].astype(float)
   val,cond=cert.sector_min_geneig(a/3,b/5)
   if val is None:return None,dims
   best=min(best,float(val))
  return best,dims
# The only source edit is accepting unbounded integer coefficients instead of the old int64 precondition.
import inspect
src=inspect.getsource(cert._operator_sym).replace('assert f.dtype == np.int64','assert f.dtype in (np.dtype(object), np.dtype(np.int64))').replace('def _operator_sym(', 'def local_operator_sym(')
exec(src,cert.__dict__)
def operator(net,f,S):return cert.local_operator_sym(net,f,S,object)

def search(desc,all_inversions=False):
 c=CoreCertificate(desc);target=.961 if desc['straight'] else .935
 val,U=c.p.minimise(restarts=2,seed=desc['pid'],sweeps=100,tol=1e-10)
 if c.n:
  ww,vv=np.linalg.eigh(U.T@U);proj=U@vv[:,-1];S=tuple(i for g in c.G if sum(proj[i] for i in g)<0 for i in g)
 else:S=()
 lam,dims=c.c_S(S);best=(lam if lam is not None else -1,S,dims);tries=1
 if best[0]<target or all_inversions:
  for bits in itertools.product([0,1],repeat=max(0,len(c.G)-1)):
   ss=tuple(i for b,g in zip((0,)+bits,c.G) if b for i in g)
   ll,dd=c.c_S(ss);tries+=1
   if ll is not None and ll>best[0]:best=(ll,ss,dd)
   if best[0]>target+1e-6 and not all_inversions:break
 return c,dict(pid=desc['pid'],straight=desc['straight'],n=c.n,numerical_min=val,bound=best[0],S=best[1],dims=best[2],tries=tries,target=target,input_bits=max(abs(int(x)).bit_length() for x in c.cur.ravel()),tensor_cells=c.cur.size)

if __name__=='__main__':
 ds=json.load(open(sys.argv[1]));part=int(sys.argv[2]) if len(sys.argv)>2 else 0;parts=int(sys.argv[3]) if len(sys.argv)>3 else 1
 with open('logs/core_cert_'+str(part)+'.jsonl','a',buffering=1) as f:
  for i,d in enumerate(ds):
   if i%parts!=part:continue
   tt=time.monotonic()
   try:
    c,r=search(d);r['index']=i;r['wall']=time.monotonic()-tt
   except Exception as e:r=dict(index=i,pid=d['pid'],error=str(e),wall=time.monotonic()-tt)
   f.write(json.dumps(r)+'\n');print(i,r,flush=True)
