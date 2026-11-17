from pathlib import Path
import subprocess, os, time, json
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED
root=Path('/home/ubuntu/aklt/wt/ARCH_0')
report=Path('/home/ubuntu/aklt/reports/ARCH_0')
lib=report/'stmt-fix-olean';lib.mkdir(exist_ok=True)
files=[root/'AKLT/Challenge/MainV2.lean',*sorted((root/'AKLT/Defs').glob('*.lean')),*sorted((root/'AKLT/Blueprint/Top').glob('*.lean'))]
mods={str(p.relative_to(root)).removesuffix('.lean').replace('/','.'):p for p in files}
# Lean selects the first root containing the AKLT prefix. Overlay read-only
# prebuilt dependencies, but never put an output symlink at an owned module.
for cache in [Path('/home/ubuntu/aklt/repo/.lake/build/lib/lean'),root/'.lake/build/lib/lean']:
 for p in (cache/'AKLT').rglob('*'):
  if not p.is_file():continue
  rel=p.relative_to(cache)
  module='.'.join((*rel.parts[:-1],rel.name.split('.')[0]))
  if module in mods:continue
  target=lib/rel;target.parent.mkdir(parents=True,exist_ok=True)
  if not target.exists():target.symlink_to(p.resolve())
import re
needs={m:set(re.findall(r'(?m)^import (\S+)',p.read_text()))&mods.keys() for m,p in mods.items()}
env=os.environ.copy();env['LEAN_PATH']=str(lib)+':'+str(root/'.lake/build/lib/lean')+':'+env.get('LEAN_PATH','')
rows=[];done=set();pending=set(mods);running={};failed=False
start=time.monotonic()
def run(m):
 out=lib/(m.replace('.','/')+'.olean');out.parent.mkdir(parents=True,exist_ok=True)
 t=time.monotonic()
 cmd=['lean','-DautoImplicit=false','-DrelaxedAutoImplicit=false','-o',str(out),str(mods[m].relative_to(root))]
 r=subprocess.run(cmd,cwd=root,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 log=report/('stmt-fix-'+m+'.log');log.write_text(r.stdout)
 return dict(module=m,exit=r.returncode,seconds=round(time.monotonic()-t,2),log=str(log),command=cmd)
with ThreadPoolExecutor(max_workers=3) as pool:
 while pending or running:
  for m in sorted(pending):
   if len(running)>=3:break
   if needs[m]<=done:
    running[pool.submit(run,m)]=m;pending.remove(m)
  if not running:
   if pending:raise RuntimeError('dependency cycle '+repr(pending))
   break
  ready,_=wait(running,return_when=FIRST_COMPLETED)
  for f in ready:
   m=running.pop(f);r=f.result();rows.append(r)
   print(m, 'PASS' if not r['exit'] else 'FAIL',r['seconds'],'s',flush=True)
   if r['exit']:
    print(Path(r['log']).read_text()[-7000:],flush=True);failed=True
   else:done.add(m)
  if failed:
   for f in running:f.cancel()
   break
(report/'stmt-fix-build.json').write_text(json.dumps(dict(wall_seconds=round(time.monotonic()-start,2),parallel_limit=3,results=rows),indent=2)+'\n')
raise SystemExit(1 if failed else 0)
