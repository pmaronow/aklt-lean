from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import subprocess, json, time, os
root=Path('/home/ubuntu/aklt/wt/GEN_PACKED')
out=Path('/home/ubuntu/aklt/reports/GEN_PACKED')
src=root/'AKLT/Gen/Packed/Bench'
src.mkdir(parents=True,exist_ok=True)
(out/'artifacts').mkdir(exist_ok=True)
pattern='d37ac9018f2e456b'
for mb in [1,10,50]:
 p=src/f'Literal{mb}MB.lean'
 count=mb*1000000*2
 with p.open('w') as f:
  f.write('import Mathlib\nnamespace AKLT.Gen.Packed.Bench.Literal'+str(mb)+'MB\n')
  f.write('def payload : Nat := 0x')
  f.write(pattern*(count//len(pattern)))
  f.write('\ntheorem lowBits : payload % 65536 = 17771 := by decide +kernel\n#print axioms lowBits\nend AKLT.Gen.Packed.Bench.Literal'+str(mb)+'MB\n')

def run(mb):
 name=f'Literal{mb}MB'
 cmd=['bash','-c','ulimit -v 41943040\nexec /usr/bin/time -v -o "$1" timeout 240 lake env lean -o "$2" "$3"','bench',str(out/(name+'.time')),str(out/'artifacts'/(name+'.olean')),str(src/(name+'.lean'))]
 env=os.environ.copy();env['PATH']=str(Path.home()/'.elan/bin')+':'+env['PATH']
 t=time.monotonic()
 with (out/(name+'.log')).open('w') as log:
  p=subprocess.run(cmd,cwd=root,env=env,stdout=log,stderr=subprocess.STDOUT)
 result={'name':name,'payload_bytes':mb*1000000,'source_bytes':(src/(name+'.lean')).stat().st_size,'exit':p.returncode,'wall':time.monotonic()-t,'olean_bytes':(out/'artifacts'/(name+'.olean')).stat().st_size if (out/'artifacts'/(name+'.olean')).exists() else None}
 (out/(name+'.json')).write_text(json.dumps(result,indent=2))
 print(json.dumps(result),flush=True)
with ThreadPoolExecutor(max_workers=3) as pool:
 list(pool.map(run,[1,10,50]))
