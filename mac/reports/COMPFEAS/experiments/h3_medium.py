from sweep import run
import concurrent.futures
jobs=[]
for ty,m,L,K,T in [('typed',9,18,24,260),('typed',9,20,28,300),('typed',10,18,20,260),('original',10,18,28,260),('typed',10,18,28,220)]:
 for X in ['B','C']:
  a=['experiments/'+('tailmem6_profile' if ty=='typed' else 'tailmem5_profile'),X,*map(str,(m,L,K,T,2*K-3,4*K-3)),'.961','.935']
  a+=['.145217','.352782','.340008','.149953','.357549','.344661','1','1.20'] if ty=='typed' else ['.18094','.36751','1','1.23']
  jobs.append((f'h3_{ty}_m{m}_L{L}_K{K}_T{T}_{X}_free',a))
  for d in ([1,2] if X=='B' else [1,2,3]):
   b=a.copy();b[5]=str(4*K-3);b[6]=str(4*K-3);b[7]=str(L);b.append(str(d))
   jobs.append((f'h3_{ty}_m{m}_L{L}_K{K}_T{T}_{X}_d{d}',b))
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as p:list(p.map(run,jobs))
