#!/usr/bin/env python3
"""Port one real part, AKLT/Cert/H2, and only its prerequisite source closure.
All changes live in the report overlay; no main/worktree source is edited.
"""
import hashlib,json,os,re,resource,subprocess,sys
from pathlib import Path
R=Path('/home/ubuntu/aklt/reports/PAL_FIT');WT=Path('/home/ubuntu/aklt/wt/PAL_FIT');P=R/'pilot'
os.sched_setaffinity(0,set(range(16)))
resource.setrlimit(resource.RLIMIT_AS,(64*1024**2,32*1024**3))
sys.path.insert(0,str(R/'tools'))
from port_modules import transform
D=json.loads((R/'clean-dependencies.json').read_text())['deps']
roots=['.'.join(p.relative_to(WT).with_suffix('').parts) for p in sorted((WT/'AKLT/Cert/H2').glob('*.lean'))]
selected=set()
def visit(m):
 if m in selected:return
 selected.add(m)
 for dep in D[m]:visit(dep)
for m in roots:visit(m)
manifest=[]
for m in sorted(selected):
 rel=Path(*m.split('.')).with_suffix('.lean');dest=P/rel;dest.parent.mkdir(parents=True,exist_ok=True)
 text=transform((WT/rel).read_text());dest.write_text(text)
 manifest.append(dict(module=m,source=str(rel),bytes=len(text.encode()),sha256=hashlib.sha256(text.encode()).hexdigest()))
(R/'pilot-h2-sources.json').write_text(json.dumps(manifest,indent=2)+'\n')
trusted=(R/'lean-path.txt').read_text().strip().split(':')[1:]
library=P/'.lake/build/lib/lean';env=':'.join([str(library),*trusted]);finished=set();failed={};records=[]
while len(finished)<len(selected):
 ready=sorted(m for m in selected-finished if set(D[m])<=finished)
 if not ready:raise RuntimeError('cyclic pilot dependencies')
 for m in ready:
  finished.add(m)
  if set(D[m]) & failed.keys():failed[m]='blocked prerequisite';continue
  rel=Path(*m.split('.'));obj=(library/rel).with_suffix('.olean')
  # Main was already built by the first pilot; no measurement is repeated.
  if m=='AKLT.Challenge.Main' and obj.is_file():continue
  obj.parent.mkdir(parents=True,exist_ok=True)
  name='pilot-h2-'+m
  cmd=[sys.executable,str(R/'tools/limited.py'),'--name',name,'--cwd',str(P),'--seconds','1200','--env','LEAN_PATH='+env,'--',
    '/home/ubuntu/.elan/toolchains/leanprover--lean4---v4.35.0-rc2/bin/lean','-j1','-DElab.async=false','-DautoImplicit=false','-DrelaxedAutoImplicit=false',str((P/rel).with_suffix('.lean')),'-o',str(obj)]
  with (R/'pilot-h2-driver.log').open('a') as log:subprocess.run(cmd,stdout=log,stderr=subprocess.STDOUT,check=False)
  row=json.loads((R/'measurements'/name/'result.json').read_text());records.append(row)
  if row['exit_code']!=0:failed[m]=row['exit_code']
  (R/'pilot-h2-result.json').write_text(json.dumps(dict(selected=len(selected),roots=roots,finished=len(finished),failed=failed,records=records),indent=2)+'\n')
(R/'pilot-h2-result.json').write_text(json.dumps(dict(selected=len(selected),roots=roots,finished=len(finished),failed=failed,records=records),indent=2)+'\n')
if not failed:
 names=[]
 for m in roots:
  src=(WT/Path(*m.split('.')).with_suffix('.lean')).read_text()
  for name in re.findall(r'^(?:theorem|lemma)\s+([A-Za-z_][A-Za-z_0-9\']*(?:\.[A-Za-z_][A-Za-z_0-9\']*)*)',src,re.M):
   names.append(name if name.startswith('AKLT.') else 'AKLT.Cert.H2.'+name)
 audit=P/'AKLT/PALFit/H2PortAudit.lean'
 audit.write_text('module\nimport AKLT.Cert.H2.All\n\n'+'\n'.join('#print axioms '+n for n in sorted(set(names)))+'\n')
 name='pilot-h2-axioms'
 cmd=[sys.executable,str(R/'tools/limited.py'),'--name',name,'--cwd',str(P),'--seconds','120','--env','LEAN_PATH='+env,'--',
  '/home/ubuntu/.elan/toolchains/leanprover--lean4---v4.35.0-rc2/bin/lean','-j1','-DwarningAsError=true',str(audit)]
 with (R/'pilot-h2-driver.log').open('a') as log:subprocess.run(cmd,stdout=log,stderr=subprocess.STDOUT,check=False)
 result=json.loads((R/'pilot-h2-result.json').read_text());result['audit_theorems']=sorted(set(names));result['audit']=json.loads((R/'measurements'/name/'result.json').read_text());(R/'pilot-h2-result.json').write_text(json.dumps(result,indent=2)+'\n')
print('pilot H2',len(selected),'modules, failures',failed)
