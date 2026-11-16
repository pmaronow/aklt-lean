import subprocess, concurrent.futures, json, time, os, resource
from pathlib import Path
root=Path(__file__).resolve().parents[1]
os.chdir(root)
def run(task):
 name,cmd=task
 t=time.monotonic()
 with open(root/'logs'/f'{name}.out','w') as out,open(root/'logs'/f'{name}.err','w') as err:
  p=subprocess.run(cmd,stdout=out,stderr=err,timeout=2400,env=dict(os.environ,OPENBLAS_NUM_THREADS='1',OMP_NUM_THREADS='1',VECLIB_MAXIMUM_THREADS='1'))
 
 for x in cmd:
  if x.startswith('PREFIX_CACHE=') and os.environ.get('KEEP_PREFIX','0')!='1':
   Path(x.split('=',1)[1]).unlink(missing_ok=True)
 r=dict(name=name,command=cmd,returncode=p.returncode,wall=time.monotonic()-t)
 print(json.dumps(r),flush=True)
 return r
if __name__=='__main__':
 import sys
 mode=sys.argv[1]
 tasks=[]
 if mode=='growth':
  for m in range(4,11):
   K=m+3
   tasks.append((f'growth_m{m}',['experiments/tailmem4_profile','B',str(m),str(m),str(K),str(m+1),str(m),str(4*K-3),'.961','.935','.18094','.36751','1','1.23']))
 elif mode=='h2':
  for m,k in [(4,1),(6,1),(6,4),(6,8),(8,1),(8,4),(8,8)]:
   tasks.append((f'h2_m{m}_k{k}',['experiments/alm_profile',str(m),str(k),'9610','9350']))
 with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
  list(pool.map(run,tasks))
