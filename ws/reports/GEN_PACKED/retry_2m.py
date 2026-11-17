from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import os,subprocess,time,json,sys
root=Path('/home/ubuntu/aklt/wt/GEN_PACKED');out=Path('/home/ubuntu/aklt/reports/GEN_PACKED');env=os.environ.copy();env['PATH']=str(Path.home()/'.elan/bin')+':'+env['PATH']
rows=[int(x) for x in sys.argv[1:]] or [1,10,100]
def run(r):
 name=f'Scale2000000R{r}'
 prior=out/(name+'-retry.json')
 if prior.exists() and json.loads(prior.read_text())['exit']==0:return
 cmd=['lake','env','/usr/bin/time','-v','-o',str(out/(name+'-retry.time')),'timeout','300','lean','-j','1','--profile','-o',str(out/'artifacts'/(name+'.olean')),f'AKLT/Gen/Packed/Bench/{name}.lean']
 t=time.monotonic()
 with (out/(name+'-retry.log')).open('w') as log:p=subprocess.run(cmd,cwd=root,env=env,stdout=log,stderr=subprocess.STDOUT)
 obj={'name':name,'exit':p.returncode,'wall':time.monotonic()-t,'retry':True,'timeout_seconds':300,'olean_bytes':(out/'artifacts'/(name+'.olean')).stat().st_size if (out/'artifacts'/(name+'.olean')).exists() else None}
 (out/(name+'-retry.json')).write_text(json.dumps(obj,indent=2));print(obj,flush=True)
with ThreadPoolExecutor(max_workers=2) as pool:list(pool.map(run,rows))
