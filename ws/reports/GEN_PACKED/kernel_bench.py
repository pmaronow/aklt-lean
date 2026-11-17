from pathlib import Path
import os,subprocess,time,json,shutil,sys
root=Path('/home/ubuntu/aklt/wt/GEN_PACKED');out=Path('/home/ubuntu/aklt/reports/GEN_PACKED');src=root/'AKLT/Gen/Packed/Bench';env=os.environ.copy();env['PATH']=str(Path.home()/'.elan/bin')+':'+env['PATH']
lib=root/'.lake/build/lib/lean/AKLT/Gen/Packed/Bench';lib.mkdir(parents=True,exist_ok=True)
for bits in ([int(x) for x in sys.argv[1:]] or [100000,1000000,2000000]):
 data=f'Scale{bits}R1'
 while not (out/(data+'.json')).exists():time.sleep(1)
 obj=json.loads((out/(data+'.json')).read_text())
 retry=out/(data+'-retry.json')
 if retry.exists() and json.loads(retry.read_text())['exit']==0:obj=json.loads(retry.read_text())
 if obj['exit']!=0: print('data unavailable',data,flush=True);continue
 shutil.copyfile(out/'artifacts'/(data+'.olean'),lib/(data+'.olean'))
 for rows in [1,10,100]:
  name=f'Kernel{bits}R{rows}'
  text=f'''import AKLT.Gen.Packed.Bench.{data}
namespace AKLT.Gen.Packed.Bench.{name}
set_option trace.profiler true in
set_option trace.profiler.threshold 0 in
 theorem checked : rowsCheck 79 {bits//80} 24 3 2 {rows} {data}.A {data}.B = true := by decide +kernel
#print axioms checked
end AKLT.Gen.Packed.Bench.{name}
'''
  p=src/(name+'.lean');p.write_text(text)
  cmd=['lake','env','/usr/bin/time','-v','-o',str(out/(name+'.time')),'timeout','60','lean','-j','1','--profile','-Dprofiler.threshold=0','-o',str(out/'artifacts'/(name+'.olean')),str(p)]
  start=time.monotonic()
  with (out/(name+'.log')).open('w') as log:r=subprocess.run(cmd,cwd=root,env=env,stdout=log,stderr=subprocess.STDOUT)
  obj={'name':name,'exit':r.returncode,'wall':time.monotonic()-start}
  (out/(name+'.json')).write_text(json.dumps(obj,indent=2));print(json.dumps(obj),flush=True)
