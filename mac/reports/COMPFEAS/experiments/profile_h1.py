import sys,os,time,json,math,resource,itertools
from pathlib import Path
root=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(root/'vendor'))
sys.path.insert(0,str(root/'programs/h1-local/code'))
import numpy as np
import ring,cert
ring.P63=str(root/'programs/data/pext/pext7962.json')
from closed_exact import certify_decoupled
from fractions import Fraction as F
P=ring.load()
records=[json.loads(l) for l in open(root/'programs/h1-local/out/certificates_covered.jsonl')]
start=time.monotonic()
stats={'contract_mul':0,'contract_add':0,'bareiss_updates':0,'bareiss_mul':0,'bareiss_sub':0,'bareiss_div':0,'pivots':0,'max_pivot_bits':0,'max_input_bits':0,'matrix_count':0,'matrix_entries':0,'max_size':0,'sum_d3':0}
orig_td=cert.itensordot
def td(A,B,axes):
 aa,bb=axes; shared=math.prod(A.shape[i] for i in aa)
 out=A.size*B.size//(shared*shared)
 stats['contract_mul']+=out*shared;stats['contract_add']+=out*max(0,shared-1)
 return orig_td(A,B,axes)
cert.itensordot=td
orig_bareiss=cert.bareiss_pd
def bp(M):
 n=len(M); stats['matrix_count']+=1;stats['matrix_entries']+=n*n;stats['max_size']=max(stats['max_size'],n);stats['sum_d3']+=n**3
 stats['max_input_bits']=max(stats['max_input_bits'],max(abs(x).bit_length() for r in M for x in r))
 A=[r[:] for r in M];prev=1
 for k in range(n):
  Ak=A[k];piv=Ak[k]
  stats['pivots']+=1;stats['max_pivot_bits']=max(stats['max_pivot_bits'],piv.bit_length())
  if piv<=0:return False,k
  for i in range(k+1,n):
   aik=Ak[i];Ai=A[i];cnt=n-i
   stats['bareiss_updates']+=cnt;stats['bareiss_mul']+=cnt*(2 if aik else 1);stats['bareiss_sub']+=cnt if aik else 0;stats['bareiss_div']+=cnt
   if aik:
    for j in range(i,n): Ai[j]=(Ai[j]*piv-aik*Ak[j])//prev
   else:
    for j in range(i,n):Ai[j]=(Ai[j]*piv)//prev
  prev=piv
 return True,None
cert.bareiss_pd=bp
out=open(root/'logs/h1_profiles.jsonl','w',buffering=1)
limit=int(sys.argv[1]) if len(sys.argv)>1 else len(records)
for i,r in enumerate(records[:limit]):
 t=time.monotonic();pid=r['pid'];p,q=map(int,r['target'].split('/'))
 before=stats.copy()
 if r['kind']=='closed':
  app,good,rad=certify_decoupled(ring.Pattern(P[pid],refined=False),F(p,q));good=good and app
  row=dict(index=i,pid=pid,kind='closed',ok=good,wall=time.monotonic()-t)
 else:
  c=cert.Certificate(P[pid],refined=False,leafred=r['leafred'])
  result=c.exact(tuple(r['S']),p,q,least_only=True)
  row=dict(index=i,pid=pid,kind='operator',ok=result['ok'],slots=c.n,scale_bits=c.net.scale.bit_length(),tensor_elements=c.cur.size,nonzero_coeff=int(np.count_nonzero(c.cur)),sectors=result['sectors'],wall=time.monotonic()-t,counts={k:stats[k]-before[k] for k in stats if not k.startswith('max_')},max_pivot_bits=stats['max_pivot_bits'],max_input_bits=stats['max_input_bits'])
 out.write(json.dumps(row)+'\n')
 if i%100==0:print(i,pid,r['kind'],'wall',time.monotonic()-start,flush=True)
 if not row['ok']:raise RuntimeError(row)
summary=dict(records=min(limit,len(records)),wall=time.monotonic()-start,maxrss_bytes=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,stats=stats)
(root/'logs/h1_summary.json').write_text(json.dumps(summary,indent=2))
print(json.dumps(summary),flush=True)
