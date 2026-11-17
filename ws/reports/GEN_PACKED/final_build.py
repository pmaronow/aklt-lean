from pathlib import Path
import subprocess,time,os,json
root=Path('/home/ubuntu/aklt/wt/GEN_PACKED');out=Path('/home/ubuntu/aklt/reports/GEN_PACKED');env=os.environ.copy();env['PATH']=str(Path.home()/'.elan/bin')+':'+env['PATH']
for mod in ['All','Example','Audit']:
 t=time.monotonic()
 with (out/('build-'+mod+'.log')).open('w') as log:p=subprocess.run(['lake','build','AKLT.Gen.Packed.'+mod],cwd=root,env=env,stdout=log,stderr=subprocess.STDOUT)
 obj={'module':mod,'exit':p.returncode,'wall':time.monotonic()-t}
 (out/('build-'+mod+'.json')).write_text(json.dumps(obj,indent=2));print(obj,flush=True)
 if p.returncode:break
