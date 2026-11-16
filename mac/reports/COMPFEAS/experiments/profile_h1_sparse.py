import os,sys,time,json,math,resource
from pathlib import Path
root=Path(__file__).resolve().parents[1];sys.path[:0]=[str(root/'vendor'),str(root/'programs/h1-local/code')]
import numpy as np
import ring,cert
ring.P63=str(root/'programs/data/pext/pext7962.json');P=ring.load()
records=[json.loads(l) for l in open(root/'programs/h1-local/out/certificates_covered_operator_only.jsonl')]
orig=cert.itensordot;stats=dict(calls=0,dense_mul=0,dense_add=0,sparse_mul=0,sparse_add=0,dense_output=0,sparse_output=0,final_coeff_dense=0,final_coeff_nonzero=0,max_value_bits=0)
def td(A,B,axes):
 ax,bx=axes;ashared=math.prod(A.shape[i] for i in ax);output=A.size*B.size//ashared**2
 ca=np.count_nonzero(A,axis=tuple(i for i in range(A.ndim) if i not in ax))
 cb=np.count_nonzero(B,axis=tuple(i for i in range(B.ndim) if i not in bx))
 ca=np.transpose(ca,[sorted(ax).index(i) for i in ax]).ravel()
 cb=np.transpose(cb,[sorted(bx).index(i) for i in bx]).ravel()
 nzprod=sum(int(a)*int(b) for a,b in zip(ca,cb));C=orig(A,B,axes);nzout=int(np.count_nonzero(C))
 stats['calls']+=1;stats['dense_mul']+=output*ashared;stats['dense_add']+=output*(ashared-1);stats['sparse_mul']+=nzprod;stats['sparse_add']+=max(0,nzprod-nzout);stats['dense_output']+=output;stats['sparse_output']+=nzout
 return C
cert.itensordot=td
out=open(root/'logs/h1_sparse_profiles.jsonl','w',buffering=1);start=time.monotonic()
for i,r in enumerate(records):
 before=stats.copy();t=time.monotonic();p=ring.Pattern(P[r['pid']],refined=False);net=cert.Net(p,leafred=r['leafred']);cur,nxt=net.cur_next_int()
 stats['final_coeff_dense']+=cur.size+nxt.size;stats['final_coeff_nonzero']+=int(np.count_nonzero(cur))+int(np.count_nonzero(nxt));stats['max_value_bits']=max(stats['max_value_bits'],int(max(cur.max(),nxt.max())).bit_length())
 out.write(json.dumps(dict(pid=r['pid'],wall=time.monotonic()-t,counts={k:stats[k]-before[k] for k in stats if not k.startswith('max_')}))+'\n')
 if i%500==0:print(i,'wall',time.monotonic()-start,flush=True)
result=dict(stats=stats,wall=time.monotonic()-start,maxrss_bytes=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
(root/'logs/h1_sparse_summary.json').write_text(json.dumps(result,indent=2));print(result)
