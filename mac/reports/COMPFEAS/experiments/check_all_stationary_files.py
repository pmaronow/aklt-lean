from sweep import run
import concurrent.futures
jobs=[]
for X,ds in [('B',[1,2]),('C',[1,2,3])]:
 for d in ds:
  name=f'stationary_{X}_m10_R70_d{d}_coarse'
  jobs.append((f'integer_file_{X}{d}',['env','AUTOMATON=data/windows_m10_min.txt','experiments/check_stationary_integer',f'data/{name}.bin.gz',X,str(d)]))
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as p:list(p.map(run,jobs))
