from sweep import run
import concurrent.futures,sys
mode=sys.argv[1];jobs=[]
if mode=='c70':
 for d in [1,2,3]:jobs.append((f'stationary_C_m10_R70_d{d}',['env','AUTOMATON=data/windows_m10_min.txt','experiments/stationary_exact','C','10','12','70','450',str(d)]))
 workers=2
elif mode=='b50':
 for d in [1,2]:jobs.append((f'stationary_B_m10_R50_d{d}',['env','AUTOMATON=data/windows_m10_min.txt','experiments/stationary_exact','B','10','12','50','450',str(d)]))
 workers=1
else:raise ValueError(mode)
with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as p:list(p.map(run,jobs))
