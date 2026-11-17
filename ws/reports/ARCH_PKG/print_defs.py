import json
import os
from pathlib import Path
import subprocess
T=Path('/home/ubuntu/aklt/wt/ARCH_PKG');R=Path('/home/ubuntu/aklt/reports/ARCH_PKG')
TC=Path('/home/ubuntu/.elan/toolchains/leanprover--lean4---v4.35.0-rc2')
env={**os.environ,'PATH':str(TC/'bin')+':'+os.environ['PATH']}
LP=subprocess.check_output([str(TC/'bin/lake'),'env','printenv','LEAN_PATH'],cwd=T,env=env,text=True).strip()
x=json.loads((R/'canonical-challenge.json').read_text())
for side,mod,path in [('challenge',x['module'],str(R/'canonical/lib')+':'+x['LEAN_PATH']),('solution','Solution',str(R/'compat/lib')+':'+LP)]:
 p=R/(side+'-print.lean')
 p.write_text(('module\nimport all '+mod if side=='challenge' else 'import '+mod)+'\nset_option pp.all true\n#print AKLT.Defs.Compass.step\n')
 with (R/(side+'-print.log')).open('w') as log:
  subprocess.run([str(TC/'bin/lean'),'-j1',str(p)],cwd=T,env={**env,'LEAN_PATH':path},stdout=log,stderr=subprocess.STDOUT)
