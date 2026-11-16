from sweep import run
import concurrent.futures
jobs=[]
for X in ['B','C']:
 for cl in ['free']+(['d1','d2'] if X=='B' else ['d1','d2','d3']):
  T,AT,NEX=(134,47,97) if cl=='free' else (97,97,12)
  cmd=['env','AUTOMATON=data/windows_m10_min.txt','experiments/tailmem6_count',X,'10','12','25',str(T),str(AT),str(NEX),'.961','.935','.145217','.352782','.340008','.150000','.357549','.344661','1','1.20']
  if cl!='free':cmd.append(cl[-1])
  jobs.append((f'h3_typedminsafe_m10_L12_K25_T134_{X}_{cl}',cmd))
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as p:list(p.map(run,jobs))
