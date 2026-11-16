import sys,time,json,resource,math
from pathlib import Path
root=Path(__file__).resolve().parents[1];sys.path[:0]=[str(root/'vendor'),str(root/'programs/h1-local/code')]
import numpy as np
import ring,cert
ring.P63=str(root/'programs/data/pext/pext7962.json');P=ring.load();records=[json.loads(l) for l in open(root/'programs/h1-local/out/certificates_covered_operator_only.jsonl')]
stats=dict(qubit_calls=0,qubit_nonzero_placements=0,qubit_nonzero_additions=0,qubit_dense_additions=0,basis_nonzero_products=0,basis_nonzero_add_upper=0,basis_dense_products=0,max_operator_entries=0,max_operator_nonzero=0,operator_entries=0,operator_nonzero=0)
qorig=cert._qubit;tdorig=np.tensordot;active=False

def qb(Re,Im):
 stats['qubit_calls']+=1;stats['qubit_nonzero_placements']+=2*(int(np.count_nonzero(Re))+int(np.count_nonzero(Im)));stats['qubit_dense_additions']+=2*Re.size
 for a,b in [(Re[0],Re[3]),(Im[0],Im[3]),(Re[1],Im[2]),(Im[1],Re[2])]:stats['qubit_nonzero_additions']+=2*int(np.count_nonzero((a!=0)&(b!=0)))
 return qorig(Re,Im)

def td(A,B,axes=2):
 if active and isinstance(axes,tuple):
  ax,bx=axes;ax=[i%A.ndim for i in ax];bx=[i%B.ndim for i in bx];sh=math.prod(A.shape[i] for i in ax);out=A.size*B.size//sh**2
  ca=np.count_nonzero(A,axis=tuple(i for i in range(A.ndim) if i not in ax)).ravel();cb=np.count_nonzero(B,axis=tuple(i for i in range(B.ndim) if i not in bx)).ravel();nonzero=sum(int(a)*int(b) for a,b in zip(ca,cb))
  stats['basis_nonzero_products']+=nonzero;stats['basis_nonzero_add_upper']+=nonzero;stats['basis_dense_products']+=out*sh
 return tdorig(A,B,axes=axes)
cert._qubit=qb;np.tensordot=td
start=time.monotonic()
for i,r in enumerate(records):
 c=cert.Certificate(P[r['pid']],refined=False,leafred=r['leafred']);active=True;A,B,q,fl=c.operators(tuple(r['S']));active=False
 for M in [A,B]:
  nz=int(np.count_nonzero(M));stats['max_operator_entries']=max(stats['max_operator_entries'],M.size);stats['max_operator_nonzero']=max(stats['max_operator_nonzero'],nz);stats['operator_entries']+=M.size;stats['operator_nonzero']+=nz
 if i%500==0:print(i,'wall',time.monotonic()-start,flush=True)
result=dict(stats=stats,wall=time.monotonic()-start,maxrss_bytes=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
(root/'logs/h1_operator_summary.json').write_text(json.dumps(result,indent=2));print(result)
