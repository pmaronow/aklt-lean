import sys,json,math
import numpy as np
import scipy.sparse as sp
from scipy.sparse.linalg import spsolve,eigs
m=int(sys.argv[1]);a=float(sys.argv[2]);out=sys.argv[3]
cs=float(sys.argv[4]) if len(sys.argv)>4 else .961;ct=float(sys.argv[5]) if len(sys.argv)>5 else .935
fn='/home/ubuntu/aklt/compfeas/data/windows_m'+str(m)+'_min.txt'
with open(fn) as f:
 nr,nq=map(int,f.readline().split())
 for i in range(nr):f.readline()
 records=[list(map(int,f.readline().split())) for i in range(nq)]
xs=1/cs;xt=1/ct;hC=1.2
ca=[.145217,.150000];cb=[.352782,.357549]
if cs!=.961 or ct!=.935:
 for k,c in enumerate([cs,ct]):
  ff=-math.log(.928*c)/(1-.928*c);cb[k]=ff/3;ca[k]=ff/3-(-math.log(.928)/(1-.928))/5
kap=[ca[0]+2*cb[0]*hC,cb[1]+(ca[1]+cb[1])*hC]
Vs=[];diags=[]
for sgx,sgy in [(1,0),(-1,0),(0,1),(0,-1)]:
 mats=[];cross=[]
 for p in range(4):
  rr=[];cc=[];vv=[];kr=[];kc=[];kv=[]
  for i,r in enumerate(records):
   ain=r[0]&3
   for d,t in enumerate(r[1:5]):
    if t<0:continue
    k=r[5+d];dx=[1,0,-1,0][d];dy=[0,1,0,-1][d];fac=math.exp(-a*(sgx*dx+sgy*dy))
    w=.2 if k==2 else ((xs/3 if k==0 else xt/3) if p==0 else (xs/3 if k==0 and p in [1,2] else 1/3))
    rr.append(i);cc.append(t);vv.append(w*fac)
    if (p==0 and k==1) or (p==1 and k==0):kr.append(i);kc.append(t);kv.append((xt/3*kap[1] if p==0 else xs/3*kap[0])*fac)
  mats.append(sp.csr_matrix((vv,(rr,cc)),shape=(nq,nq)));cross.append(sp.csr_matrix((kv,(kr,kc)),shape=(nq,nq)))
 eig=float(eigs(mats[0],k=1,which='LM',return_eigenvectors=False)[0].real)
 zs=np.zeros((4,nq));I=sp.eye(nq,format='csc')
 for p in [3,2]:
  z=np.ones(nq)
  for it in range(20000):
   nz=np.maximum(1,mats[p]@z)
   if np.max(nz-z)<1e-13:break
   z=nz
  # Add a positive resolvent correction to certify a numerical strict residual.
  z+=1e-9*spsolve(I-mats[p],np.ones(nq))
  zs[p]=z
 for p in [1,0]:zs[p]=spsolve(I-mats[p],cross[p]@zs[2 if p==0 else 3]+1e-9*np.ones(nq))
 res=min(np.min(zs[p]-mats[p]@zs[p]-(cross[p]@zs[2 if p==0 else 3] if p<2 else 0)) for p in range(4))
 if np.min(zs)<0:raise RuntimeError('negative vector')

 Vs.append(zs);diags.append(dict(sign=[sgx,sgy],eigenvalue=eig,min_residual=float(res),maximums=np.max(zs,axis=1).tolist()))
np.array(Vs,dtype=np.float64).tofile(out)
print(json.dumps(dict(m=m,a=a,states=nq,cs=cs,ct=ct,diagnostics=diags),indent=2))
