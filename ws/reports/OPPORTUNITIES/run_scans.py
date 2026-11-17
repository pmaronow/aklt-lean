import concurrent.futures as cf
import json
import resource
import subprocess
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent
OUT = ROOT / 'experiments'

def limit():
    resource.setrlimit(resource.RLIMIT_AS, (7*1024**3, 7*1024**3))
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))

def run(args):
    tag = '_'.join(map(str,args))
    start=time.monotonic()
    with (OUT/(tag+'.log')).open('w') as f, (OUT/(tag+'.err')).open('w') as e:
        cmd=['/usr/bin/time','-v','-o',str(OUT/(tag+'.time')),str(OUT/str(args[0])),*map(str,args[1:])]
        p=subprocess.run(cmd,stdout=f,stderr=e,preexec_fn=limit,timeout=240)
    return dict(args=args,wall=time.monotonic()-start,exit=p.returncode,log=tag+'.log')

if __name__=='__main__':
    jobs=[['alm',m,k,9610,9350] for m,k in [(2,1),(4,1),(6,1),(8,1),(2,6),(2,8),(4,4),(4,6),(4,8),(6,2),(6,4),(6,6)]]
    with cf.ThreadPoolExecutor(max_workers=3) as ex:
        for r in ex.map(run,jobs):
            print(json.dumps(r),flush=True)
