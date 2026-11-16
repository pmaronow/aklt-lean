from sweep import run
from pathlib import Path
import concurrent.futures
root=Path(__file__).resolve().parents[1];jobs=[]
for K,T,baseT in [(25,130,140),(25,134,140),(25,136,140),(24,184,200),(26,116,120)]:
 for X in ['B','C']:
  for d in ([1,2] if X=='B' else [1,2,3]):
   dst=root/'logs'/f'h3_typedminsafe_m10_L12_K{K}_T{T}_{X}_d{d}.out';src=root/'logs'/f'h3_typedminsafe_m10_L12_K{K}_T{baseT}_{X}_d{d}.out'
   dst.write_text(src.read_text())
  cmd=['env','AUTOMATON=data/windows_m10_min.txt',f'PREFIX_CACHE=data/prefix/typedminsafe_m10_L12_K{K}_{X}_free.bin','experiments/tailmem6_cached',X,'10','12',str(K),str(T),str(2*K-3),str(4*K-3),'.961','.935','.145217','.352782','.340008','.150000','.357549','.344661','1','1.20']
  jobs.append((f'h3_typedminsafe_m10_L12_K{K}_T{T}_{X}_free',cmd))
with concurrent.futures.ThreadPoolExecutor(max_workers=1) as p:list(p.map(run,jobs))
