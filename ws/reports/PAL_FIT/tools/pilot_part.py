#!/usr/bin/env python3
"""Build a small complete part in the report overlay, reusing only successful pilot prerequisites."""
import hashlib,json,os,re,resource,subprocess,sys
from pathlib import Path
R=Path('/home/ubuntu/aklt/reports/PAL_FIT');WT=Path('/home/ubuntu/aklt/wt/PAL_FIT');P=R/'pilot'
os.sched_setaffinity(0,set(range(16)));resource.setrlimit(resource.RLIMIT_AS,(64*1024**2,32*1024**3))
sys.path.insert(0,str(R/'tools'));from port_modules import transform
part=sys.argv[1];tag=part.replace('/','-');D=json.loads((R/'clean-dependencies.json').read_text())['deps'];selected=set()
roots=['.'.join(p.relative_to(WT).with_suffix('').parts) for p in sorted((WT/part).glob('*.lean'))]
def visit(m):
 if m in selected:return
 selected.add(m)
 for d in D[m]:visit(d)
for m in roots:visit(m)
manifest=[]
for m in sorted(selected):
 rel=Path(*m.split('.')).with_suffix('.lean');dest=P/rel;dest.parent.mkdir(parents=True,exist_ok=True)
 text=transform((WT/rel).read_text())
 if dest.is_file():assert dest.read_text()==text,m
 else:dest.write_text(text)
 manifest.append(dict(module=m,source=str(rel),sha256=hashlib.sha256(text.encode()).hexdigest()))
(R/('pilot-'+tag+'-sources.json')).write_text(json.dumps(manifest,indent=2)+'\n')
lib=P/'.lake/build/lib/lean';env=':'.join([str(lib),*(R/'lean-path.txt').read_text().strip().split(':')[1:]])
records=[];failed={};done=set();reused=[]
def measure(name,args,seconds=1200):
 cmd=[sys.executable,str(R/'tools/limited.py'),'--name',name,'--cwd',str(P),'--seconds',str(seconds),'--env','LEAN_PATH='+env,'--',*args]
 with (R/('pilot-'+tag+'-driver.log')).open('a') as log:subprocess.run(cmd,stdout=log,stderr=subprocess.STDOUT,check=False)
 return json.loads((R/'measurements'/name/'result.json').read_text())
def save():
 (R/('pilot-'+tag+'-result.json')).write_text(json.dumps(dict(part=part,roots=roots,selected=len(selected),finished=len(done),reused=reused,failed=failed,records=records),indent=2)+'\n')
while len(done)<len(selected):
 for m in sorted(m for m in selected-done if set(D[m])<=done):
  done.add(m)
  if set(D[m]) & failed.keys():failed[m]='blocked prerequisite';save();continue
  rel=Path(*m.split('.'));obj=(lib/rel).with_suffix('.olean')
  if obj.is_file():reused.append(m);save();continue
  obj.parent.mkdir(parents=True,exist_ok=True)
  row=measure('pilot-part-'+m,['/home/ubuntu/.elan/toolchains/leanprover--lean4---v4.35.0-rc2/bin/lean','-j1','-DElab.async=false','-DautoImplicit=false','-DrelaxedAutoImplicit=false',str((P/rel).with_suffix('.lean')),'-o',str(obj)])
  records.append(row)
  if row['exit_code']!=0:failed[m]=row['exit_code']
  save()
# Existing audit modules print every public theorem for Gram. Defs' only named
# theorem is printed using its exact namespace; data definitions add no axioms.
if not failed:
 names=[]
 for m in roots:
  src=(WT/Path(*m.split('.')).with_suffix('.lean')).read_text()
  ns=re.findall(r'^namespace\s+(\S+)',src,re.M);namespace=ns[0] if ns else ''
  names.extend((n if n.startswith('AKLT.') else namespace+'.'+n) for n in re.findall(r'^(?:theorem|lemma)\s+([A-Za-z_][A-Za-z_0-9\']*)',src,re.M))
 audit=P/'AKLT/PALFit'/('PartAudit'+tag.replace('-','')+'.lean');audit.parent.mkdir(parents=True,exist_ok=True)
 audit.write_text('module\n'+''.join('import '+m+'\n' for m in roots)+'\n'+''.join('#print axioms '+n+'\n' for n in sorted(set(names))))
 row=measure('pilot-part-audit-'+tag,['/home/ubuntu/.elan/toolchains/leanprover--lean4---v4.35.0-rc2/bin/lean','-j1','-DwarningAsError=true',str(audit)],120)
 result=json.loads((R/('pilot-'+tag+'-result.json')).read_text());result.update(audit_theorems=sorted(set(names)),audit=row);(R/('pilot-'+tag+'-result.json')).write_text(json.dumps(result,indent=2)+'\n')
print(part,'selected',len(selected),'failed',failed)
