import json, os, pathlib, subprocess, time
base=pathlib.Path('/home/ubuntu/aklt/reports/FIX_STAR')
runs=['q017','round2-q037','round2-q038','round2-survey']
while not all((base/r/'names.txt').is_file() for r in runs): time.sleep(1)
modules=['AKLT.W.Q017.Main','AKLT.W.Q016.Main','AKLT.W.Q020.Main','AKLT.W.Q037.Main','AKLT.W.Q038.Main']
lines=[f'import {m}' for m in modules]+['']
roots=[]
for r in runs:
    for name in (base/r/'names.txt').read_text().splitlines():
        if name and name not in roots:
            roots.append(name);lines.extend([f'#check {name}',f'#print axioms {name}'])
source=base/'round2-Verify.lean';source.write_text('\n'.join(lines)+'\n')
env=dict(os.environ);env['PATH']='/home/ubuntu/.elan/bin:'+env.get('PATH','')
start=time.monotonic()
with (base/'round2-verify.log').open('w') as log, (base/'round2-verify.time').open('w') as timing:
    rc=subprocess.run(['/usr/bin/time','-f','verify time_s=%e peak_rss_kb=%M','lake','env','lean',str(source)],cwd='/home/ubuntu/aklt/wt/FIX_STAR',env=env,stdout=log,stderr=timing).returncode
result=dict(exit=rc,root_count=len(roots),time_s=round(time.monotonic()-start,2),modules=modules)
(base/'round2-verify-result.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result),flush=True)
