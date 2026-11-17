from run_scans import run
import concurrent.futures as cf
import json

coeffs=[.145217,.352782,.340008,.149953,.357549,.344661,1,1.2]
jobs=[]
for m,L,K,T in [(6,14,12,280),(8,14,16,240),(8,18,16,240),(8,20,20,260)]:
    for X in ['B','C']:
        jobs.append(['tail',X,m,L,K,T,2*K-3,4*K-3,.961,.935,*coeffs,-1])
if __name__=='__main__':
    with cf.ThreadPoolExecutor(max_workers=2) as ex:
        for r in ex.map(run,jobs): print(json.dumps(r),flush=True)
