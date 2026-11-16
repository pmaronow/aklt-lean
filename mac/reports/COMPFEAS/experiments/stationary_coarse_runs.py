from sweep import run
import concurrent.futures
jobs=[]
for X,d in [('B',2),('C',1),('C',2),('C',3)]:
 name=f'stationary_{X}_m10_R70_d{d}_coarse'
 jobs.append((name,['env','AUTOMATON=data/windows_m10_min.txt',f'CERT_OUTPUT=data/{name}.bin.gz','experiments/stationary_exact16',X,'10','12','70','450',str(d)]))
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as p:list(p.map(run,jobs))
