import os,sys,time,math,json,resource
from pathlib import Path
root=Path(__file__).resolve().parents[1]
sys.path[:0]=[str(root/'vendor'),str(root/'programs/h1-local/code')]
import numpy as np
import ring,cert
ring.P63=str(root/'programs/data/pext/pext7962.json')
P=ring.load();records=[json.loads(l) for l in open(root/'programs/h1-local/out/certificates_covered.jsonl')]
start=time.monotonic();out=open(root/'logs/h1_chol.jsonl','w',buffering=1)
current=None
stats=dict(blocks=0,raw_dd=0,weighted_dd=0,chol=0,failures=0,max_size=0,max_factor_bits=0,max_matrix_bits=0,total_factor_entries=0,total_products=0)
def bp(M):
 n=len(M);stats['blocks']+=1;stats['max_size']=max(stats['max_size'],n)
 g=math.gcd(*(abs(x) for r in M for x in r));g=max(1,g)
 a=[[x//g for x in row] for row in M]
 bits=max(abs(x).bit_length() for r in a for x in r);stats['max_matrix_bits']=max(stats['max_matrix_bits'],bits)
 raw=min(a[i][i]-sum(abs(a[i][j]) for j in range(n) if j!=i) for i in range(n))
 row=dict(pid=current,n=n,gcd=g,matrix_bits=bits,raw_dd=raw>0)
 if raw>0:
  stats['raw_dd']+=1;out.write(json.dumps(row)+'\n');return True,None
 arr=np.array(a,dtype=float)
 scale=float(max(a[i][i] for i in range(n)))
 mineig=float(np.linalg.eigvalsh(arr/scale)[0]*scale)
 row['lambda_est']=mineig
 if mineig<=0:
  stats['failures']+=1;row['failure']='float_eigen';out.write(json.dumps(row)+'\n');return True,None
 # use a rational diagonal shift, selected only to generate a witness
 exponent=math.floor(math.log2(mineig))-2
 # Scale a by a small power of two if the shift is fractional, so B is integer.
 den=2**max(0,-exponent); delta=2**max(0,exponent)
 b=[[x*den for x in r] for r in a]
 chol=np.linalg.cholesky(np.array(b,dtype=float)-delta*np.eye(n))
 for p in [0,4,8,12,16,20,24,28]:
  S=2**p;LL=np.rint(chol*S).astype(object)
  LL=np.array([[int(x) for x in r] for r in LL],dtype=object)
  # Candidate generation may be floating point; this check is exact integers only.
  B=np.array(b,dtype=object)*(S*S)-LL@LL.T
  margins=[int(B[i,i])-sum(abs(int(B[i,j])) for j in range(n) if j!=i) for i in range(n)]
  if min(margins)>0:
   factorbits=max(abs(int(x)).bit_length() for x in LL.flat)
   row.update(precision=p,factor_bits=factorbits,shift_den=den,delta=delta,min_margin=min(margins),cert_entries=n*(n+1)//2,products=n*(n+1)*(n+2)//6)
   stats['chol']+=1;stats['max_factor_bits']=max(stats['max_factor_bits'],factorbits);stats['total_factor_entries']+=n*(n+1)//2;stats['total_products']+=n*(n+1)*(n+2)//6
   # Store representative small / large witnesses, not the whole production set.
   if current in [5420,7697] or (n>=200 and not (root/'data/h1_large_chol.json').exists()):
    (root/'data'/f'h1_chol_{current}_{n}.json').write_text(json.dumps(dict(row,M=a,L=LL.tolist())))
    if n>=200:(root/'data/h1_large_chol.json').write_text(json.dumps(dict(row,M=a,L=LL.tolist())))
   out.write(json.dumps(row)+'\n');return True,None
 stats['failures']+=1;row['failure']='precision';out.write(json.dumps(row)+'\n');return True,None
cert.bareiss_pd=bp
ops=[r for r in records if r['kind']=='operator']
if len(sys.argv)>1:
 ids=set(map(int,sys.argv[1:]));ops=[r for r in ops if r['pid'] in ids]
for i,r in enumerate(ops):
 current=r['pid'];p,q=map(int,r['target'].split('/'))
 c=cert.Certificate(P[current],refined=False,leafred=r['leafred'])
 res=c.exact(tuple(r['S']),p,q,least_only=True)
 if not res['ok']:raise RuntimeError((current,res))
 if i%100==0:print(i,current,'wall',time.monotonic()-start,stats,flush=True)
summary=dict(wall=time.monotonic()-start,maxrss_bytes=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,stats=stats)
(root/'logs/h1_chol_summary.json').write_text(json.dumps(summary,indent=2))
print(summary)
