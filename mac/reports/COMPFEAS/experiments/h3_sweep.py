from sweep import run
import concurrent.futures,sys
mode=sys.argv[1]
configs=[]
if mode=='coarse':
 configs=[('original',6,14,12,400),('original',8,14,12,260),('original',8,16,16,260),('typed',6,14,12,400),('typed',8,14,12,260),('typed',8,16,16,260)]
else: raise ValueError(mode)
tasks=[]
for ty,m,L,K,T in configs:
 for X in ['B','C']:
  args=['experiments/'+('tailmem6_profile' if ty=='typed' else 'tailmem5_profile'),X,*map(str,(m,L,K,T,2*K-3,4*K-3)),'.961','.935']
  args+=['.145217','.352782','.340008','.149953','.357549','.344661','1','1.20'] if ty=='typed' else ['.18094','.36751','1','1.23']
  tasks.append((f'h3_{ty}_m{m}_L{L}_K{K}_T{T}_{X}_free',args))
  for d in ([1,2] if X=='B' else [1,2,3]):
   a=args.copy();a[5]=str(4*K-3);a[6]=str(4*K-3);a[7]=str(L);a.append(str(d))
   tasks.append((f'h3_{ty}_m{m}_L{L}_K{K}_T{T}_{X}_d{d}',a))
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
 list(pool.map(run,tasks))
