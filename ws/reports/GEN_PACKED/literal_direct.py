from pathlib import Path
import os, subprocess, json, time
root=Path('/home/ubuntu/aklt/wt/GEN_PACKED');out=Path('/home/ubuntu/aklt/reports/GEN_PACKED')
env=os.environ.copy();env['PATH']=str(Path.home()/'.elan/bin')+':'+env['PATH']
for mb in [1,10,50]:
 name=f'Literal{mb}MB-direct'
 cmd=['lake','env','/usr/bin/time','-v','-o',str(out/(name+'.time')),'timeout','60','lean','-j','1','--profile','-Dprofiler.threshold=0','-o',str(out/'artifacts'/f'Literal{mb}MB.olean'),f'AKLT/Gen/Packed/Bench/Literal{mb}MB.lean']
 t=time.monotonic()
 with (out/(name+'.log')).open('w') as log:
  p=subprocess.run(cmd,cwd=root,env=env,stdout=log,stderr=subprocess.STDOUT)
 obj={'name':name,'exit':p.returncode,'wall':time.monotonic()-t,'payload_bytes':mb*1000000}
 (out/(name+'.json')).write_text(json.dumps(obj,indent=2));print(json.dumps(obj),flush=True)
