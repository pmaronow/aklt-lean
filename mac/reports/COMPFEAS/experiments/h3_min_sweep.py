from sweep import run
import concurrent.futures,os,sys
from pathlib import Path
mode=sys.argv[1]
configs={'first': [('typedminsafe',9,18,36,300),('typedminsafe',10,16,28,220),('typedminsafe',10,18,24,220),('typedminsafe',11,16,20,200)],
 'parity': [('typedminsafe',10,12,24,180),('typedminsafe',10,12,24,200),('typedminsafe',10,12,25,140),('typedminsafe',10,12,25,160),('typedminsafe',10,12,26,120),('typedminsafe',10,12,26,140),('typedminsafe',11,13,22,160)],
 'refine': [('typedminsafe',10,12,26,160),('typedminsafe',10,12,26,200),('typedminsafe',10,12,28,140),('typedminsafe',10,12,28,180),('typedminsafe',9,11,48,300)],
 'cheap': [('typedminsafe',10,10,24,220),('typedminsafe',10,12,24,220),('typedminsafe',10,10,28,220),('typedminsafe',11,11,20,200)],
 'second': [('typedminsafe',9,16,40,300),('typedminsafe',10,14,28,220),('typedminsafe',11,14,20,200),('originalmin',10,20,28,260)]}[mode]
Path('data/prefix').mkdir(exist_ok=True)
jobs=[]
for ty,m,L,K,T in configs:
 for X in ['B','C']:
  a=['experiments/'+('tailmem6_cached' if ty.startswith('typed') else 'tailmem5_cached'),X,*map(str,(m,L,K,T,2*K-3,4*K-3)),'.961','.935']
  a+=['.145217','.352782','.340008','.150000','.357549','.344661','1','1.20'] if ty.startswith('typed') else ['.18094','.36751','1','1.23']
  for cl in ['free']+(['d1','d2'] if X=='B' else ['d1','d2','d3']):
   b=a.copy()
   if cl!='free':b[5]=str(4*K-3);b[6]=str(4*K-3);b[7]=str(L);b.append(cl[-1])
   cmd=['env',f'AUTOMATON=data/windows_m{m}_min.txt',f'PREFIX_CACHE=data/prefix/{ty}_m{m}_L{L}_K{K}_{X}_{cl}.bin']+b
   jobs.append((f'h3_{ty}_m{m}_L{L}_K{K}_T{T}_{X}_{cl}',cmd))
with concurrent.futures.ThreadPoolExecutor(max_workers=int(os.environ.get("SWEEP_WORKERS","2"))) as p:list(p.map(run,jobs))
