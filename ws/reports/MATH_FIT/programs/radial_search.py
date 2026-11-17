import sys,json,math
import numpy as np
import scipy.sparse as sp
from scipy.sparse.linalg import eigs,spsolve
from pathlib import Path
ls=Path('data/windows_m10_min.txt').read_text().splitlines();nr,nq=map(int,ls[0].split());rs=np.array([list(map(int,l.split())) for l in ls[nr+1:]],dtype=int);T=rs[:,1:5];K=rs[:,5:9];dx=np.array([1,0,-1,0]);dy=np.array([0,1,0,-1]);hc=1.2
wa=np.where(K==2,.2,np.where(K==0,1/.961/3,1/.935/3));wc=np.where(K==2,.2,np.where(K==0,1/.961/3,1/3));wd=np.where(K==2,.2,1/3);weights=[wa,wc,wc,wd];kapS=.145217+2*.352782*hc;kapT=.357549+(.150000+.357549)*hc;crossA=np.where(K==1,1/.935/3*kapT,0);crossB=np.where(K==0,1/.961/3*kapS,0)
vs=[];chis=[];diags=[]
for p,w in enumerate(weights):
 row=[];col=[];val=[]
 for d in range(4):
  ok=T[:,d]>=0;row.extend(np.where(ok)[0]);col.extend(T[ok,d]);val.extend(w[ok,d])
 W=sp.csr_matrix((val,(row,col)),shape=(nq,nq));lam=float(eigs(W,k=1,which='LM',return_eigenvectors=False)[0].real);q=lam+.001;v=spsolve(q*sp.eye(nq,format='csc')-W,np.ones(nq));v/=v.max();mass=W@v;P=sp.diags(np.divide(1,mass,out=np.zeros(nq),where=mass>0))@W@sp.diags(v);drift=np.zeros((nq,2))
 for d in range(4):
  ok=T[:,d]>=0;u=np.zeros(nq);u[ok]=w[ok,d]*v[T[ok,d]];u=np.divide(u,mass,out=np.zeros(nq),where=mass>0);drift[:,0]+=u*dx[d];drift[:,1]+=u*dy[d]
 chi=np.column_stack([spsolve(sp.eye(nq,format='csc')-P,drift[:,k]) for k in range(2)])
 err=np.max(np.abs((sp.eye(nq)-P)@chi-drift));vs.append(v);chis.append(chi);diags.append(dict(phase=p,lambda_=lam,q=q,vmin=float(v.min()),max_chi=float(np.abs(chi).max()),drift_error=float(err)))
v=np.array(vs);chi=np.array(chis);results=[]
# Try rational powers: A,B use exponent 1, C,D 2; also slower half powers as a diagnostic.
for ks in [[1,1,2,2],[.5,.5,1.5,1.5],[.5,.5,1,1]]:
 for smooth in [1,4,16]:
  for RR in [6,8,10,12,16,20]:
   pos=set()
   for rad in [RR,RR+1,RR+2,RR+4,2*RR,4*RR,100]:
    for t in range(49):
     ang=2*np.pi*t/48;xx=int(round(rad*np.cos(ang)));yy=int(round(rad*np.sin(ang)))
     if max(abs(xx),abs(yy))>=RR:pos.add((xx,yy))
   maxdiag=np.zeros(4);maxcross=np.zeros(2)
   for x,y in pos:
    base=smooth+(x+chi[:,:,0])**2+(y+chi[:,:,1])**2;F=v/base**np.array(ks)[:,None];sums=np.zeros((4,nq));cs=np.zeros((2,nq))
    for d in range(4):
     ok=T[:,d]>=0;dest=T[ok,d];D=smooth+(x+dx[d]+chi[:,dest,0])**2+(y+dy[d]+chi[:,dest,1])**2;FF=v[:,dest]/D**np.array(ks)[:,None]
     for p in range(4):sums[p,ok]+=weights[p][ok,d]*FF[p]
     cs[0,ok]+=crossA[ok,d]*FF[2];cs[1,ok]+=crossB[ok,d]*FF[3]
    ratios=np.divide(sums,F);maxdiag=np.maximum(maxdiag,ratios.max(axis=1))
    for p in range(2):
     gap=F[p]-sums[p]
     if np.any((gap<=0)&(cs[p]>0)):maxcross[p]=np.inf
     elif not np.isinf(maxcross[p]):maxcross[p]=max(maxcross[p],float(np.max(np.divide(cs[p],gap,out=np.zeros(nq),where=gap>0))))
   row=dict(powers=ks,smooth=smooth,R=RR,maxdiag=maxdiag.tolist(),required_AB_over_CD=maxcross.tolist());results.append(row);print(json.dumps(row),flush=True)
Path('data/radial_search.json').write_text(json.dumps(dict(gauges=diags,results=results),indent=2));np.savez('data/radial_gauges.npz',v=v,chi=chi)
