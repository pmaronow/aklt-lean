import sys,json,math,time,resource
import numpy as np
from pathlib import Path
sys.path.insert(0,'programs');import core_cert as cc
D=json.load(open('data/cores_True.json'))
R={r['index']:r for r in map(json.loads,open('logs/core_cert_0.jsonl'))}
# Normalize scalar arrays too; the search-only adapter had no tensor axes in the zero-slot cases.
_orig=cc.CoreCertificate.__init__
def init(self,d):
 _orig(self,d);self.cur=np.asarray(self.cur,dtype=object);self.nxt=np.asarray(self.nxt,dtype=object)
cc.CoreCertificate.__init__=init
start=time.monotonic();stats=dict(cases=0,scalar_cases=0,blocks=0,raw_dd=0,gram=0,max_dimension=0,matrix_entries=0,gram_products=0,gram_entries=0,max_matrix_bits=0,max_factor_bits=0,tensor_cells=0,tensor_nonzeros=0,failures=[])
with open('data/core_certificates.jsonl','w',buffering=1) as out,open('logs/core_exact.jsonl','w',buffering=1) as log:
 for i,d in enumerate(D):
  tt=time.monotonic();c=cc.CoreCertificate(d);p,q=(961,1000) if d['straight'] else (187,200)
  st=dict(index=i,pid=d['pid'],n=c.n)
  stats['cases']+=1;stats['tensor_cells']+=c.cur.size+c.nxt.size;stats['tensor_nonzeros']+=np.count_nonzero(c.cur)+np.count_nonzero(c.nxt)
  if c.n==0:
   M=5*q*int(c.cur)-3*p*int(c.nxt);assert M>=0;stats['scalar_cases']+=1
   out.write(json.dumps(dict(index=i,pid=d['pid'],scalar=M,cur=int(c.cur),next=int(c.nxt)))+'\n');st['scalar']=M
  else:
   r=R.get(i,{})
   if 'S' not in r:
    raise RuntimeError(('missing search',i,r))
   S=r['S'];(A,sec,fa),(B,sec2,fb)=c.ops(S)
   assert all(v==0 for v in fa.values()) and all(v==0 for v in fb.values()),(i,fa,fb)
   assert np.array_equal(sec,sec2)
   mask=sec[:,None]!=sec[None,:];assert all(x==0 for x in A[mask]) and all(x==0 for x in B[mask])
   forms=[]
   for s in cc.cert.sector_list(sec,True):
    ids=np.where(sec==s)[0];a=A[np.ix_(ids,ids)];b=B[np.ix_(ids,ids)];M=5*q*a-3*p*b;n=len(ids)
    g=math.gcd(*(int(x) for x in M.flat));assert g>0;N=np.array([[int(x)//g for x in row] for row in M],dtype=object);assert np.array_equal(g*N,M)
    bits=max(abs(int(x)).bit_length() for x in N.flat);stats['max_matrix_bits']=max(stats['max_matrix_bits'],bits);stats['max_dimension']=max(stats['max_dimension'],n);stats['matrix_entries']+=n*n;stats['blocks']+=1
    form=dict(sector=int(s),n=n,g=g,M=N.tolist(),bits=bits)
    dd=min(int(N[j,j])-sum(abs(int(N[j,k])) for k in range(n) if k!=j) for j in range(n))
    if dd>0:form.update(kind='dd',margin=dd);stats['raw_dd']+=1
    else:
     arr=np.array(N,dtype=float);scale=max(float(x) for x in np.diag(arr));ev=float(np.linalg.eigvalsh(arr/scale)[0]*scale);assert ev>0,(i,ev)
     exp=math.floor(math.log2(ev))-2;den=2**max(0,-exp);delta=2**max(0,exp);Q=N*den
     chol=np.linalg.cholesky(np.array(Q,dtype=float)-delta*np.eye(n))
     good=False
     for prec in [0,4,8,12,16,20,24,28,32]:
      ll=np.rint(chol*2**prec);L=np.array([[int(x) for x in row] for row in ll],dtype=object);E=Q*2**(2*prec)-L@L.T
      margin=min(int(E[j,j])-sum(abs(int(E[j,k])) for k in range(n) if k!=j) for j in range(n))
      if margin>0:
       good=True;form.update(kind='gram',den=den,S=2**prec,L=L.tolist(),margin=margin);stats['gram']+=1;stats['gram_products']+=n*(n+1)*(n+2)//6;stats['gram_entries']+=n*(n+1)//2;stats['max_factor_bits']=max(stats['max_factor_bits'],max(abs(int(x)).bit_length() for x in L.flat));break
     assert good,('gram failed',i,n)
    forms.append(form)
   out.write(json.dumps(dict(index=i,pid=d['pid'],S=S,forms=forms))+'\n');st['forms']=[dict(n=f['n'],kind=f['kind'],bits=f['bits']) for f in forms]
  st['wall']=time.monotonic()-tt;log.write(json.dumps(st)+'\n')
  if i%50==0:print(i,st,'total',time.monotonic()-start,flush=True)
stats['tensor_nonzeros']=int(stats['tensor_nonzeros']);stats['wall']=time.monotonic()-start;stats['maxrss_KiB']=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss;stats['witness_bytes']=Path('data/core_certificates.jsonl').stat().st_size
Path('data/core_exact_summary.json').write_text(json.dumps(stats,indent=2));print(json.dumps(stats,indent=2))
