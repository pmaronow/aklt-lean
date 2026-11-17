#!/usr/bin/env python3
"""End-to-end protected component verification; registry metadata stays separate.

All mutable artifacts are under --work. The production cgroup must enclose this
whole process. This does not claim Palomar's authenticated supervisor verdict.
"""
import argparse,datetime,hashlib,json,os,re,shutil,subprocess,sys,time
from pathlib import Path
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[1]

class ConronCapacity(RuntimeError):pass

class Pipeline:
 def __init__(self,a):
  self.a=a;self.work=a.work.resolve()
  self.config_path=ROOT/('verification/regression/comparator.json' if a.regression_inputs else 'comparator.json')
  self.challenge_source=ROOT/('verification/regression/Challenge.lean.in' if a.regression_inputs else 'Challenge.lean')
  self.solution_module='Regression.Solution' if a.regression_inputs else 'Solution'
  self.audit_module='Regression.Audit' if a.regression_inputs else 'Audit'
  if self.work.is_relative_to(ROOT):raise RuntimeError('--work must be outside the source root')
  self.work.mkdir(parents=True,exist_ok=True);self.started=time.monotonic()
  cpus=sorted(os.sched_getaffinity(0))[:16];assert len(cpus)==16;os.sched_setaffinity(0,cpus)
  self.env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1','GIT_TERMINAL_PROMPT':'0','LEAN_ABORT_ON_PANIC':'1','LEAN_NUM_THREADS':str(a.build_threads)}
  for key in ['LAKE_PKG_URL_MAP','LEAN_PATH','LEAN_SRC_PATH','LEAN_SYSROOT']:self.env.pop(key,None)
  self.env['ELAN_TOOLCHAIN']=(ROOT/'lean-toolchain').read_text().strip()
  self.receipt={'scope':'protected component pipeline; not registry acceptance or authenticated Palomar capacity evidence',
   'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'project':str(ROOT),'stages':[],
   'status':'running','budget_seconds':a.budget,'build_threads':a.build_threads,'affinity_cpus':cpus,
   'source_commit':subprocess.check_output(['git','-C',str(ROOT),'rev-parse','HEAD'],text=True).strip(),
   'dirty':bool(subprocess.check_output(['git','-C',str(ROOT),'status','--porcelain'],text=True))}
  self.receipt['source_sha256']=self.source_hashes()
  if self.receipt['dirty'] and not a.existing_dependencies:raise RuntimeError('Cold verification requires a clean committed clone')
  self.save()
 def source_hashes(self):
  result={}
  for directory,dirs,files in os.walk(ROOT):
   dirs[:]=[x for x in dirs if x not in ['.git','.lake']]
   for name in files:
    if name.endswith('.lean'):
     f=Path(directory)/name;result[str(f.relative_to(ROOT))]=hashlib.sha256(f.read_bytes()).hexdigest()
  return result
 def save(self):
  self.receipt['elapsed_s']=time.monotonic()-self.started
  (self.work/'receipt.json').write_text(json.dumps(self.receipt,indent=2)+'\n')
 def run(self,name,args,*,cwd=ROOT,env=None,allow_failure=False,timeout=None):
  remain=self.a.budget-(time.monotonic()-self.started) if self.a.budget>0 else None
  if remain is not None and remain<1:raise RuntimeError('The shared execution budget is exhausted')
  self.receipt['current_stage']=name;self.save();out=self.work/'stages'/name
  cmd=[sys.executable,str(ROOT/'scripts/measure_stage.py'),'--stage',name,'--out',str(out),'--cwd',str(cwd),
   '--timeout',str(min(x for x in [remain,timeout] if x is not None and x>0) if any(x is not None and x>0 for x in [remain,timeout]) else 0),'--rss-cap-gb',str(self.a.rss_cap_gb),'--address-space-gib',str(self.a.address_space_gib)]
  if self.a.campaign_report:cmd+=['--campaign-report',str(self.a.campaign_report)]
  cmd+=['--',*map(str,args)]
  with (self.work/'driver.log').open('a') as log:subprocess.run(cmd,cwd=ROOT,env={**self.env,**(env or {})},stdout=log,stderr=subprocess.STDOUT,check=False)
  result=json.loads((out/'result.json').read_text());self.receipt['stages'].append(result);self.save()
  if (result['exit_code'] or result['limit']) and not allow_failure:raise RuntimeError(name+' failed; see '+str(out))
  return result,out
 def sha(self,path):
  h=hashlib.sha256()
  with path.open('rb') as f:
   for block in iter(lambda:f.read(4*1024**2),b''):h.update(block)
  return h.hexdigest()
 def verify(self):
  a=self.a;sys.path.insert(0,str(a.verifier.resolve()));from scripts import verify_submission as official
  tc=Path(subprocess.check_output(['lean','--print-prefix'],cwd=ROOT,env=self.env,text=True).strip()).resolve()
  self.env['PATH']=str(tc/'bin')+':'+self.env['PATH'];lean=tc/'bin/lean';lake=tc/'bin/lake'
  for name in ['home','tmp','cache']:(self.work/name).mkdir(exist_ok=True)
  self.env.update(HOME=str(self.work/'home'),TMPDIR=str(self.work/'tmp'),XDG_CACHE_HOME=str(self.work/'cache'),MATHLIB_CACHE_DIR=str(self.work/'mathlib-cache'))
  # The local metadata checker deliberately records author-owned TODOs without
  # letting them hide a mechanical source/configuration failure.
  source_result,out=self.run('source-configuration',[sys.executable,ROOT/'scripts/verify_sources.py','--verifier',a.verifier,'--report',self.work/'source-checks.json'],allow_failure=True)
  if source_result.get('limit'):raise RuntimeError('Source/configuration check stopped: '+str(source_result['limit']))
  source=json.loads((self.work/'source-checks.json').read_text());allowed={'package.metadata_todo','package.license_missing'}
  ours=[x for x in source['issues'] if x['code'] not in allowed]
  if ours:raise RuntimeError('Mechanical source/configuration findings: '+str(ours))
  self.receipt['author_metadata_findings']=source['issues'];self.receipt['source_files']=source['summary']['files_checked']
  self.receipt['verification_surface']='two-input regression' if a.regression_inputs else 'unconditional complete theorem'
  self.receipt['generated_modules_missing']=source['generated_missing']
  if source['generated_missing'] and not a.regression_inputs:
   self.receipt['status']='pending-generated-certificates';self.save()
   raise RuntimeError(str(len(source['generated_missing']))+' generated modules must be regenerated or installed before full verification; see verification/generated-modules.json')
  # Full preparation enforces more metadata requirements, including ORCIDs.
  try:official.submission_contract.load_formalization_metadata(ROOT/'formalization.yaml')
  except Exception as e:self.receipt['official_metadata_diagnostic']=str(e)
  self.save()
  if not a.existing_dependencies:
   # Only a new clone may enter this branch. No update hooks are run.
   if (ROOT/'.lake').exists():raise RuntimeError('Cold dependency setup requires an absent .lake directory')
   code='''import os,sys\nfrom pathlib import Path\nsys.dont_write_bytecode=True\nsys.path.insert(0,sys.argv[1])\nfrom scripts import verify_submission as v\np=Path(sys.argv[2]);v.materialize_packages(p,checkout=p,base_env=os.environ.copy())\n'''
   self.run('pinned-dependency-fetch',[sys.executable,'-c',code,str(a.verifier.resolve()),str(ROOT)])
   packages=ROOT/'.lake/packages';mathlib=packages/'mathlib';nested=mathlib/'.lake/packages';nested.parent.mkdir(exist_ok=True)
   nested.symlink_to(packages,target_is_directory=True)
   self.run('pinned-mathlib-cache',[lake,'exe','cache','get'],cwd=mathlib,timeout=7200)
   self.run('cache-no-build-preflight',[lake,'--no-build','build','Mathlib'])
  manifest=json.loads((ROOT/'lake-manifest.json').read_text());pins=[]
  for entry in manifest['packages']:
   path=(ROOT/'.lake/packages'/entry['name']).resolve();head=subprocess.check_output(['git','-C',str(path),'rev-parse','HEAD'],text=True).strip()
   if head!=entry['rev']:raise RuntimeError('Dependency pin mismatch: '+entry['name'])
   pins.append({'name':entry['name'],'rev':head,'path':str(path)})
  self.receipt['dependencies']=pins
  lp=subprocess.check_output([str(lake),'env','printenv','LEAN_PATH'],cwd=ROOT,env=self.env,text=True).strip()
  paths=[str((ROOT/Path(x)).resolve()) if not Path(x).is_absolute() else str(Path(x).resolve()) for x in lp.split(os.pathsep) if x]
  paths=[x for x in paths if Path(x).is_dir()]
  project_lib=(ROOT/'.lake/build/lib/lean').resolve();trusted=[x for x in paths if Path(x)!=project_lib]
  if str(tc/'lib/lean') not in trusted:trusted.append(str(tc/'lib/lean'))
  own=official.lean_source_files(ROOT)
  _,out=self.run('lean-header-parser',[lean,'--deps-json',*own],env={'LEAN_PATH':os.pathsep.join(paths)})
  header=json.loads((out/'stdout.log').read_text());entries=header.get('imports',[])
  if not entries or any(x.get('errors') or not x.get('result',{}).get('isModule') for x in entries):raise RuntimeError('Lean parsed a non-module header')
  self.receipt['parsed_header_records']=len(entries)
  if not a.skip_build:self.run('default-build',[lake,'build',*(['Handwritten','Regression.Solution','Challenge','AuditHandwritten','Regression.Audit'] if a.regression_inputs else [])])
  self.run('explicit-targets',[lake,'build',*(['Challenge','Regression.Solution','Regression.Audit'] if a.regression_inputs else ['Challenge','Solution','Audit'])])
  _,audit=self.run('strict-audit',[lake,'env','lean','-j1','-DautoImplicit=false','-DrelaxedAutoImplicit=false','-DwarningAsError=true',self.audit_module.replace('.','/')+'.lean'])
  self.run('axiom-transcript',[sys.executable,ROOT/'scripts/check_axioms.py',audit/'stdout.log','--mode','regression' if a.regression_inputs else 'full'])
  # Install the official source-pinned bubblewrap locally if the system lacks it.
  bwrap=a.bwrap.resolve() if a.bwrap else Path(shutil.which('bwrap') or '/nonexistent')
  version=subprocess.run([str(bwrap),'--version'],capture_output=True,text=True).stdout.strip() if bwrap.is_file() else ''
  if version!='bubblewrap 0.12.0':
   setup=self.work/'build-tools';setup_env={}
   if not shutil.which('meson') or not shutil.which('ninja'):
    self.run('build-tool-bootstrap',[sys.executable,'-m','pip','install','--disable-pip-version-check','--no-input','--no-cache-dir','--target',setup,'meson==1.9.2','ninja==1.13.0'])
    setup_env={'PYTHONPATH':str(setup),'PATH':str(setup/'bin')+':'+self.env['PATH']}
   if subprocess.run(['pkg-config','--exists','libcap'],check=False).returncode:
    debs=self.work/'build-debs';debs.mkdir();self.run('libcap-headers-fetch',['apt-get','download','libcap-dev'],cwd=debs)
    sysroot=self.work/'build-sysroot';sysroot.mkdir();self.run('libcap-headers-unpack',['dpkg-deb','-x',next(debs.glob('libcap-dev_*.deb')),sysroot])
    pc=next(sysroot.rglob('libcap.pc'));actual_lib=pc.parent.parent.relative_to(sysroot)
    pc.write_text(re.sub(r'^libdir=.*$', 'libdir=/'+str(actual_lib),pc.read_text(),flags=re.M))
    setup_env.update(PKG_CONFIG_PATH=str(pc.parent),PKG_CONFIG_SYSROOT_DIR=str(sysroot))
   install=self.work/'trusted-tools'
   self.run('pinned-bubblewrap-build',['bash',a.verifier/'scripts/install_bwrap.sh',install],env=setup_env,timeout=600);bwrap=install/'bwrap'
  self.receipt['bubblewrap']={'path':str(bwrap),'sha256':self.sha(bwrap),'version':subprocess.check_output([str(bwrap),'--version'],text=True).strip()}
  # The maintainer's checker pin is independent of the source compiler pin.
  from scripts.checker_updates import selected_revision,materialize_checker
  toolchain=(ROOT/'lean-toolchain').read_text().strip();revision=selected_revision(toolchain)
  conron=tc/'bin/con-ron'
  if revision:
   candidate=tc.parent/('leanprover--lean4---'+revision['release_tag'])/'bin/con-ron'
   if candidate.is_file() and self.sha(candidate)==revision['binary_sha256']:conron=candidate
   else:
    self.run('pinned-conron-download',[sys.executable,'-c',
     'import sys;from pathlib import Path;sys.path.insert(0,sys.argv[1]);from scripts.checker_updates import materialize_checker;materialize_checker(sys.argv[2],Path(sys.argv[3]),Path(sys.argv[4]))',
     str(a.verifier.resolve()),toolchain,str(conron),str(self.work/'trusted-checker-update')],timeout=600)
    conron=self.work/'trusted-checker-update/con-ron'
   if self.sha(conron)!=revision['binary_sha256']:raise RuntimeError('con-ron checksum mismatch')
  self.receipt['conron']={'path':str(conron),'sha256':self.sha(conron),'revision':revision}
  config=official.load_comparator_config(self.config_path);protected=self.work/'protected-comparator.json'
  official.protected_comparator_config(self.config_path,protected,kernels={'nanoda':[str(tc/'bin/nanoda_bin')]})
  alias=json.loads(protected.read_text())['challenge_module'];can=self.work/'canonical';src=can/'src';lib=can/'lib'
  source=src/Path(*alias.split('.')).with_suffix('.lean');obj=lib/Path(*alias.split('.')).with_suffix('.olean')
  source.parent.mkdir(parents=True);obj.parent.mkdir(parents=True);source.write_bytes(self.challenge_source.read_bytes())
  home=can/'home';tmp=can/'tmp';home.mkdir();tmp.mkdir()
  system=sorted({p.resolve() for p in map(Path,['/usr','/bin','/lib','/lib64']) if p.exists()})
  base={'PATH':str(tc/'bin')+':/usr/bin:/bin','HOME':str(home),'TMPDIR':str(tmp),'LEAN_ABORT_ON_PANIC':'1',
        'LEAN_PATH':os.pathsep.join(trusted),'LEAN_SRC_PATH':str(src)}
  def outer(command,*,cwd,read,writable=(),env=base,nested=False):
   return official.bwrap_command(list(map(str,command)),bwrap=bwrap,writable_directories=list(writable),
    readable_paths=sorted(set([*read,*official.system_readable_paths()])),executable_paths=sorted({tc,bwrap,*system}),
    environment=env,readable_directories=[cwd],nested_sandbox=nested)
  cmd=outer([lean,'-j1','-DautoImplicit=false','-DrelaxedAutoImplicit=false','--root='+str(src),source,'-o',obj],cwd=src,
    read=[src,*(Path(x['path']) for x in pins),*map(Path,trusted)],writable=[lib,home,tmp])
  self.run('protected-challenge-build',cmd,cwd=src)
  artifacts=official.canonical_challenge_artifacts(obj,module_system=True)
  if not all(p.is_file() for p in artifacts):raise RuntimeError('Missing canonical Challenge sidecar')
  targets=official.comparator_export_targets(config,official.primitive_targets(tc));exports=self.work/'exports';exports.mkdir()
  for side,module,lps in [('challenge',alias,[str(lib),*trusted]),('solution',self.solution_module,paths)]:
   env={**base,'LEAN_PATH':os.pathsep.join(lps)}
   cmd=outer([tc/'bin/leanexport',module,'--',*targets],cwd=src,read=[*(Path(x['path']) for x in pins),*map(Path,lps)],writable=[home,tmp],env=env)
   _,out=self.run(side+'-export',cmd,cwd=src)
   target=exports/(side+'.ndjson');os.link(out/'stdout.log',target);official.verify_export(target)
   self.receipt[side+'_export']={'path':str(target),'bytes':target.stat().st_size,'sha256':self.sha(target)};self.save()
  judge=self.work/'judge';(judge/'project').mkdir(parents=True);(judge/'home').mkdir();(judge/'tmp').mkdir()
  env={'PATH':base['PATH'],'HOME':str(judge/'home'),'TMPDIR':str(judge/'tmp'),'LEAN_ABORT_ON_PANIC':'1','COMPARATOR_BWRAP':str(bwrap)}
  cmd=outer([lake,'comparator','--config',protected,'--challenge-from-export',exports/'challenge.ndjson','--solution-from-export',exports/'solution.ndjson'],
    cwd=judge/'project',read=[protected,exports/'challenge.ndjson',exports/'solution.ndjson'],writable=[judge],env=env,nested=True)
  _,out=self.run('protected-comparator',cmd,cwd=judge/'project')
  transcript=(out/'stdout.log').read_text()
  if 'nanoda kernel accepts the solution' not in transcript or 'Lean default kernel accepts the solution' not in transcript:raise RuntimeError('Comparator lacks both kernel acceptance markers')
  self.receipt['mandatory_kernels_accept']=True;self.save()
  replay=self.work/'conron';replay.mkdir();env={'PATH':base['PATH'],'HOME':str(home),'TMPDIR':str(tmp)}
  cmd=outer([conron,'--verified','--jobs='+str(official.CON_RON_JOBS),exports/'solution.ndjson'],cwd=replay,
    read=[exports/'solution.ndjson',conron],writable=[home,tmp],env=env)
  result,out=self.run('conron-replay',cmd,cwd=replay,timeout=a.conron_timeout,allow_failure=True)
  from scripts.kernel_outcomes import con_ron_outcome
  outcome=con_ron_outcome(result['exit_code'],(out/'stdout.log').read_text(),(out/'stderr.log').read_text())
  self.receipt['conron_outcome']=outcome
  self.receipt['conron_accept']=outcome['status']=='accepted'
  if not self.receipt['conron_accept']:
   def events(raw):
    return {x.split()[0]:int(x.split()[1]) for x in raw.splitlines() if len(x.split())==2}
   before=events(result.get('cgroup_before',{}).get('memory.events',''))
   after=events(result.get('cgroup',{}).get('memory.events',''))
   killed=after.get('oom_kill',0)>before.get('oom_kill',0)
   if result.get('limit')=='wall_timeout' or killed:
    self.receipt['local_capacity_evidence']={'stage_deadline':result.get('timeout_s'),'wall_limit':result.get('limit'),
      'oom_kill_before':before.get('oom_kill',0),'oom_kill_after':after.get('oom_kill',0),
      'authenticated_by_palomar':False}
    raise ConronCapacity('Mandatory kernels accept; con-ron is locally capacity-inconclusive. Official supervision must authenticate the classification.')
   raise RuntimeError('Mandatory kernels accept, but con-ron did not finish accepting; retain its diagnostics for the orchestrator')
  if self.source_hashes()!=self.receipt['source_sha256']:raise RuntimeError('Lean source changed during verification')
  self.receipt['status']='all-mechanical-components-pass';self.receipt['metadata_fields_complete']=not self.receipt['author_metadata_findings'] and not self.receipt.get('official_metadata_diagnostic');self.receipt['registry_preparation_required']=True;self.receipt['submission_ready']=False;self.save()

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--verifier',type=Path,required=True);ap.add_argument('--work',type=Path,required=True)
 ap.add_argument('--budget',type=float,default=0,help='Optional shared wall watchdog; zero disables it');ap.add_argument('--build-threads',type=int,default=8);ap.add_argument('--rss-cap-gb',type=float,default=285);ap.add_argument('--address-space-gib',type=float,default=240)
 ap.add_argument('--regression-inputs',action='store_true',help='Check the retained two-input reduction before certificates are regenerated')
 ap.add_argument('--conron-timeout',type=float,default=0,help='Optional con-ron wall watchdog; zero disables it')
 ap.add_argument('--existing-dependencies',action='store_true',help='Local iteration only; cold-verify.sh never uses this')
 ap.add_argument('--skip-build',action='store_true',help='Local iteration after a separately measured fresh default build')
 ap.add_argument('--bwrap',type=Path);ap.add_argument('--campaign-report',type=Path);a=ap.parse_args();p=Pipeline(a)
 try:p.verify();return 0
 except ConronCapacity as e:p.receipt.update(status='mandatory-pass-conron-capacity-inconclusive',error=str(e),submission_ready=False);p.save();print(str(e),file=sys.stderr);return 2
 except Exception as e:p.receipt.update(status='incomplete',error=str(e));p.save();print(str(e),file=sys.stderr);return 1
if __name__=='__main__':raise SystemExit(main())
