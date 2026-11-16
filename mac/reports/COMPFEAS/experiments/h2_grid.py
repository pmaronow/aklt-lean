from sweep import run
import concurrent.futures
jobs=[]
for m in range(1,7):
 for k in [1,2,4,6,8,10]:
  if m+k>15:continue
  jobs.append((f'h2grid_m{m}_k{k}',['experiments/alm_profile',str(m),str(k),'9610','9350']))
with concurrent.futures.ThreadPoolExecutor(max_workers=1) as pool:list(pool.map(run,jobs))
