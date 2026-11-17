#!/usr/bin/env python3
"""Continue diagnostic stages serially after the clean-build lock is released."""
import hashlib
import json
import os
from pathlib import Path
import resource
import shutil
import subprocess
import sys
import time
sys.dont_write_bytecode=True
R=Path('/home/ubuntu/aklt/reports/PAL_FIT')
WT=Path('/home/ubuntu/aklt/wt/PAL_FIT')
ROOT=R/'candidate'
TC=Path('/home/ubuntu/.elan/toolchains/leanprover--lean4---v4.35.0-rc2')
LEAN=str(TC/'bin/lean')
LIMIT=str(R/'tools/limited.py')
# This orchestration process adds only a 128 MiB memory reservation.
os.sched_setaffinity(0,set(range(16)))
resource.setrlimit(resource.RLIMIT_AS,(128*1024**2,32*1024**3))

def wait_clean():
 while True:
  try:
   x=json.loads((R/'clean-build/result.json').read_text())
   if x.get('finished'):return x
  except (FileNotFoundError,json.JSONDecodeError):pass
  time.sleep(2)

def limited(name,argv,cwd=ROOT,seconds=1800,env=None,stdout=None,worker_gib=31):
 (R/'active-stage.txt').write_text(name+'\n'+time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime())+'\n')
 cmd=[sys.executable,LIMIT,'--name',name,'--cwd',str(cwd),'--seconds',str(seconds),'--worker-gib',str(worker_gib)]
 for k,v in (env or {}).items():cmd+=['--env',k+'='+str(v)]
 if stdout:cmd+=['--stdout',str(stdout)]
 cmd+=['--',*map(str,argv)]
 with (R/'after-core-driver.log').open('a') as log:
  subprocess.run(cmd,stdout=log,stderr=subprocess.STDOUT,check=False)
 return json.loads((R/'measurements'/name/'result.json').read_text())

def build(name,path,overlay=None,strict=False):
 out=(overlay or ROOT/'.lake/build/lib/lean')/path.with_suffix('.olean')
 out.parent.mkdir(parents=True,exist_ok=True)
 args=[LEAN,'-j1','-DautoImplicit=false','-DrelaxedAutoImplicit=false']
 if strict:args+=['-DwarningAsError=true']
 return limited(name,[*args,'-o',out,path],cwd=R/'pilot' if overlay else ROOT,seconds=1200,env=ENV)

initial=wait_clean()
if initial['failed'] or initial['blocked']:
 with (R/'resume-driver.log').open('w') as log:
  e=os.environ.copy();e['PAL_FIT_RESUME']='1'
  subprocess.run([sys.executable,str(R/'tools/build_core.py')],env=e,stdout=log,stderr=subprocess.STDOUT,check=False)
basepaths=(R/'lean-path.txt').read_text().strip().split(':')[1:]
project_library=ROOT/'.lake/build/lib/lean'
if not (project_library/'AKLT/PALFit/Solution.olean').is_file():
 # Keep this diagnostic separate: a cached H2 proof is not a clean-build pass.
 # Its exact closure is still sent through the independent kernels below.
 warm=R/'warm-overlay'
 shutil.copytree(project_library,warm,dirs_exist_ok=True)
 original=WT/'.lake/build/lib/lean/AKLT/Cert/H2/Check.olean'
 if not (warm/'AKLT/Cert/H2/Check.olean').is_file() and original.is_file():
  dest=warm/'AKLT/Cert/H2/Check.olean';dest.parent.mkdir(parents=True,exist_ok=True)
  shutil.copyfile(original,dest)
  (R/'warm-reuse.json').write_text(json.dumps({'reason':'H2 source compilation did not complete under conservative virtual-address limits; not clean-build evidence','cached_module':'AKLT.Cert.H2.Check','from':str(original),'sha256':hashlib.sha256(dest.read_bytes()).hexdigest(),'source_sha256':hashlib.sha256((ROOT/'AKLT/Cert/H2/Check.lean').read_bytes()).hexdigest()},indent=2)+'\n')
  deps=json.loads((R/'clean-dependencies.json').read_text())['deps']
  visited=set()
  def complete(module):
   if module in visited:return
   visited.add(module)
   for dep in deps[module]:complete(dep)
   obj=warm/Path(*module.split('.')).with_suffix('.olean')
   if obj.is_file():return
   src=ROOT/Path(*module.split('.')).with_suffix('.lean');obj.parent.mkdir(parents=True,exist_ok=True)
   limited('warm-'+module,[LEAN,'-j1','-DautoImplicit=false','-DrelaxedAutoImplicit=false',src,'-o',obj],seconds=1200,env={'LEAN_PATH':':'.join([str(warm),*basepaths])})
  complete('AKLT.PALFit.Solution')
  complete('AKLT.W.H3C026.DeadMask')
  complete('AKLT.Cert.H2.Check')
  project_library=warm
LP=':'.join([str(project_library),*basepaths])
ENV={'LEAN_PATH':LP}
# Record a canonical compilation attempt: no candidate project library in LEAN_PATH.
sys.path.insert(0,'/home/ubuntu/dbl/scratch/PAL-DRY/tools/PalomarSubmission')
from scripts import verify_submission as official
canonical_alias=official.protected_challenge_module(json.loads((ROOT/'comparator.json').read_text()))
canonical_source=R/'canonical/src'/Path(*canonical_alias.split('.')).with_suffix('.lean')
canonical_source.parent.mkdir(parents=True,exist_ok=True)
canonical_source.write_bytes((ROOT/'AKLT/PALFit/Challenge.lean').read_bytes())
(R/'canonical-alias.json').write_text(json.dumps({'module':canonical_alias,'source':str(canonical_source)},indent=2)+'\n')
limited('canonical-challenge-compile',[LEAN,'-j1','-DautoImplicit=false','--root='+str(R/'canonical/src'),canonical_source,'-o',R/'canonical-challenge.olean'],seconds=120,env={'LEAN_PATH':':'.join(basepaths)})
# Real outer/nested production namespace policy is not available in this session.
limited('sandbox-probe',['/usr/bin/bwrap','--ro-bind','/','/','--unshare-user','--unshare-pid','--proc','/proc','--','/usr/bin/true'],seconds=30,worker_gib=1)
# Audit the selected theorem and all 416 leaf proof inputs under strict warnings.
if (project_library/'AKLT/PALFit/Solution.olean').is_file():
 build('strict-audit',Path('AKLT/PALFit/Audit.lean'),strict=True)
 worktree_output=WT/'.lake/build/lib/lean/AKLT/PALFit/Solution.olean'
 worktree_output.parent.mkdir(parents=True,exist_ok=True)
 limited('worktree-solution-build',[LEAN,'-j1','-DautoImplicit=false','-DrelaxedAutoImplicit=false',WT/'AKLT/PALFit/Solution.lean','-o',worktree_output],cwd=WT,seconds=1200,env=ENV)
# An exact isolated H2 Lean reduction. It adds no hypothesis and uses no unlimited heartbeat option.
probe=Path('AKLT/PALFit/Probes/H2Complete.lean')
probeobj=R/'probe-lib'/probe.with_suffix('.olean')
probeobj.parent.mkdir(parents=True,exist_ok=True)
limited('h2-isolated-lean',[LEAN,'-j1','-DautoImplicit=false','-DrelaxedAutoImplicit=false',R/'probes'/probe,'-o',probeobj],cwd=R/'probes',seconds=1200,env=ENV)
# Pilot is one dependency-closed part directory, never a whole-tree conversion.
pilotlib=R/'pilot/.lake/build/lib/lean'
original_env=ENV
ENV={'LEAN_PATH':':'.join([str(pilotlib),*basepaths])}
for file in ['Main','MainV2','Sanity']:
 build('pilot-'+file,Path('AKLT/Challenge')/(file+'.lean'),overlay=pilotlib)
# Isolate the important private-in-exposed-definition migration issue.
fixture_base = R/'pilot/AKLT/PALFit'
fixture_base.mkdir(parents=True,exist_ok=True)
for suffix,compat in [('Strict',''),('Compat','set_option backward.privateInPublic true\n')]:
 fixture = fixture_base/('Visibility'+suffix+'.lean')
 fixture.write_text('module\npublic import Init\n\n@[expose] public section\n'+compat+
                    'namespace AKLT.PALFit.Visibility'+suffix+'\n'+
                    'private def hidden : Nat := 7\ndef visible : Nat := hidden\n'+
                    'theorem checked : visible = 7 := rfl\n#print axioms checked\n'+
                    'end AKLT.PALFit.Visibility'+suffix+'\n')
 build('visibility-'+suffix,Path('AKLT/PALFit')/fixture.name,overlay=pilotlib)
audit=R/'pilot/AKLT/PALFit/PilotAudit.lean';audit.parent.mkdir(parents=True,exist_ok=True)
import re
names=re.findall(r'^theorem\s+([A-Za-z_][A-Za-z_0-9]*)', (R/'pilot/AKLT/Challenge/Sanity.lean').read_text(), re.M)
audit.write_text('module\nimport AKLT.Challenge.Sanity\n\n'+'\n'.join('#print axioms AKLT.Challenge.'+name for name in names)+'\n')
build('pilot-axioms',Path('AKLT/PALFit/PilotAudit.lean'),overlay=pilotlib,strict=True)
ENV=original_env
# Official source and header checks, including unused nongenerated support modules.
limited('source-checks-final',[sys.executable,R/'tools/source_check.py',ROOT,R/'source-checks-final.json'],seconds=120)
files=sorted(ROOT.rglob('*.lean'));files=[p for p in files if '.lake' not in p.parts]
headers=[]
for i in range(0,len(files),64):
 name='headers-'+str(i//64).zfill(2)
 row=limited(name,[LEAN,'--deps-json',*files[i:i+64]],seconds=120)
 if row['exit_code']==0:
  data=json.loads((R/'measurements'/name/'stdout.log').read_text())
  headers.extend(data.get('imports',[]))
(R/'parsed-headers.json').write_text(json.dumps(headers,indent=2)+'\n')
# Export exactly the official primitive roots and selected solution/hazard declarations.
sys.path.insert(0,'/home/ubuntu/dbl/scratch/PAL-DRY/tools/PalomarSubmission')
from scripts import verify_submission as official
config=json.loads((ROOT/'comparator.json').read_text())
primitives=official.primitive_targets(TC)
targets=official.comparator_export_targets(config,primitives)
(R/'export-targets.json').write_text(json.dumps(targets,indent=2)+'\n')
exports=[]
for name,module,roots in [
 ('solution','AKLT.PALFit.Solution',targets),
 ('h2','AKLT.Cert.H2.Check',[*primitives,'Quot','Quot.mk','Quot.lift','Quot.ind','propext','Classical.choice','Quot.sound','AKLT.Cert.H2.complete_checked']),
 ('deadmask','AKLT.W.H3C026.DeadMask',[*primitives,'Quot','Quot.mk','Quot.lift','Quot.ind','propext','Classical.choice','Quot.sound','AKLT.W.H3C026.deadMask_proved'])]:
 path=R/(name+'.ndjson')
 row=limited(name+'-export',[TC/'bin/leanexport',module,'--',*dict.fromkeys(roots)],seconds=1800,env=ENV,stdout=path)
 if row['exit_code']==0:exports.append((name,path))
manifest=[]
for name,path in exports:
 h=hashlib.sha256()
 with path.open('rb') as stream:
  for b in iter(lambda:stream.read(8*1024**2),b''):h.update(b)
 manifest.append(dict(name=name,path=str(path),bytes=path.stat().st_size,sha256=h.hexdigest()))
(R/'exports.json').write_text(json.dumps(manifest,indent=2)+'\n')
# Comparator plumbing only: same export both sides; never an independent statement audit.
# A failed sandbox attempt cannot be interpreted as proof rejection.
if any(n=='solution' for n,_ in exports):
 path=R/'solution.ndjson'
 protected=R/'self-comparison-control.json'
 protected.write_text(json.dumps({**config,'external_kernels':{'nanoda':[str(TC/'bin/nanoda_bin')]}},indent=2)+'\n')
 limited('comparator-control',[TC/'bin/lake','comparator','--config',protected,'--challenge-from-export',path,'--solution-from-export',path],seconds=1200,env={'ELAN_TOOLCHAIN':'leanprover/lean4:v4.35.0-rc2'},worker_gib=7.5)
# Run the real checkers directly as additional diagnostics, without the unavailable sandbox.
conron=Path('/home/ubuntu/.elan/toolchains/leanprover--lean4---v4.36.0-rc1/bin/con-ron')
assert hashlib.sha256(conron.read_bytes()).hexdigest()=='4e5616d94374cae37324dad2594f6230c2bb2297240249fc78ff508f3bc5acef'
for name,path in exports:
 limited(name+'-lean-replay',[TC/'bin/leanchecker','--from-export',path],seconds=3600)
 cfg=R/(name+'-nanoda.json')
 cfg.write_text(json.dumps(dict(use_stdin=False,export_file_path=str(path),permitted_axioms=['propext','Classical.choice','Quot.sound'],unpermitted_axiom_hard_error=True,num_threads=4,nat_extension=True,string_extension=True,print_success_message=True),indent=2)+'\n')
 limited(name+'-nanoda',[TC/'bin/nanoda_bin',cfg],seconds=3600)
 limited(name+'-conron',[conron,'--verified','--jobs=2','--progress=1000',path],seconds=1800)
(R/'after-core.done').write_text(time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime())+'\n')
