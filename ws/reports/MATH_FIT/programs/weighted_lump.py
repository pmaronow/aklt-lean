import sys,json,math
import numpy as np
import scipy.sparse as sp
from scipy.sparse.linalg import eigs,spsolve
from pathlib import Path

def load(m):
 ls=Path('/home/ubuntu/aklt/compfeas/data/windows_m'+str(m)+'_min.txt').read_text().splitlines();nr,nq=map(int,ls[0].split());mp={int(l.split()[0]):int(l.split()[1]) for l in ls[1:nr+1]};rs=np.array([list(map(int,l.split())) for l in ls[nr+1:]],dtype=int);return mp,rs
mp,rs=load(10);nq=len(rs);rr=[];cc=[];vs=[]
for q,row in enumerate(rs):
 for d,t in enumerate(row[1:5]):
  if t<0:continue
  k=row[5+d];w=.2 if k==2 else (1/.961/3 if k==0 else 1/.935/3);rr.append(q);cc.append(t);vs.append(w)
W=sp.csr_matrix((vs,(rr,cc)),shape=(nq,nq));lam=float(eigs(W,k=1,which='LM',return_eigenvectors=False)[0].real)
results=[]
for shift in [.00001,.0001,.001,.005,.02]:
 v=spsolve((lam+shift)*sp.eye(nq,format='csc')-W,np.ones(nq));v/=v.max()
 assert np.min(v)>0
 for m in [6,7,8,9]:
  cm,crs=load(m);nc=len(crs);A=np.zeros((nc,4))
  for code,q in mp.items():
   c=cm[code&((1<<(2*m))-1)];row=rs[q]
   for d,t in enumerate(row[1:5]):
    if t<0:continue
    k=row[5+d];w=.2 if k==2 else (1/.961/3 if k==0 else 1/.935/3);A[c,d]=max(A[c,d],w*v[t]/v[q])
  ar=[];ac=[];av=[]
  for c,row in enumerate(crs):
   for d,t in enumerate(row[1:5]):
    if t>=0 and A[c,d]>0:ar.append(c);ac.append(t);av.append(A[c,d])
  WW=sp.csr_matrix((av,(ar,ac)),shape=(nc,nc));growth=float(eigs(WW,k=1,which='LM',return_eigenvectors=False)[0].real);results.append(dict(m=m,coarse_states=nc,shift=shift,gauge_min=float(v.min()),coarse_growth=growth,max_row=float(A.sum(axis=1).max())))
print(json.dumps(dict(full_growth=lam,results=results),indent=2));Path('data/weighted_lump.json').write_text(json.dumps(dict(full_growth=lam,results=results),indent=2))
