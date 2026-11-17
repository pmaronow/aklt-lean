#!/usr/bin/env python3
"""Clone an exact release commit and run only that clone's verification code."""
import argparse,datetime,json,os,re,resource,subprocess,sys,tempfile,time
from pathlib import Path

def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--repository',required=True,help='Package Git URL or local repository; never the parent AKLT repository')
 ap.add_argument('--commit',required=True,help='Full immutable package commit')
 ap.add_argument('--verifier',type=Path,required=True)
 ap.add_argument('--verifier-commit',default='14aa8d6b3c2f14a8540605e37144560b9a00e7e7')
 ap.add_argument('--output',type=Path,help='Fresh output directory, outside the source repository')
 ap.add_argument('--budget',type=float,default=19800)
 ap.add_argument('--build-threads',type=int,default=1,help='Lean runtime workers; serial build is the low-memory default')
 a=ap.parse_args();start=time.monotonic();cpus=sorted(os.sched_getaffinity(0))[:16]
 if len(cpus)!=16:raise SystemExit('Exactly 16 available CPUs are required')
 os.sched_setaffinity(0,cpus)
 if not re.fullmatch(r'[0-9a-f]{40}',a.commit):raise SystemExit('--commit must be a full lowercase SHA-1')
 work=a.output.resolve() if a.output else Path(tempfile.mkdtemp(prefix='aklt-cold-verify-'))
 if a.output:
  if work.exists():raise SystemExit('--output must not already exist')
  work.mkdir(parents=True)
 verifier=a.verifier.resolve();vpin=subprocess.check_output(['git','-C',str(verifier),'rev-parse','HEAD'],text=True).strip()
 if vpin!=a.verifier_commit:raise SystemExit('Official verifier revision differs from --verifier-commit')
 env={**os.environ,'GIT_TERMINAL_PROMPT':'0','PYTHONDONTWRITEBYTECODE':'1','ELAN_TOOLCHAIN':'leanprover/lean4:v4.35.0-rc2'}
 for key in ['LAKE_PKG_URL_MAP','LEAN_PATH','LEAN_SRC_PATH','LEAN_SYSROOT']:env.pop(key,None)
 env['PATH']=str(Path.home()/'.elan/bin')+':'+env.get('PATH','')
 receipt={'scope':'cold protected-component verification, not Palomar registry acceptance',
  'status':'cloning','started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
  'repository':a.repository,'commit':a.commit,'verifier_commit':vpin,'affinity_cpus':cpus,'budget_seconds':a.budget}
 def save():
  receipt['wall_s']=time.monotonic()-start;(work/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
 save();clone=work/'clone';before=resource.getrusage(resource.RUSAGE_CHILDREN);clock=time.monotonic()
 def run(args):
  with (work/'bootstrap.log').open('a') as log:subprocess.run(list(map(str,args)),env=env,stdout=log,stderr=subprocess.STDOUT,check=True,timeout=max(1,a.budget-(time.monotonic()-start)))
 try:
  run(['git','-c','core.hooksPath=/dev/null','-c','gc.auto=0','clone','--no-checkout','--no-hardlinks',a.repository,clone])
  run(['git','-C',clone,'-c','core.hooksPath=/dev/null','checkout','--detach',a.commit])
  actual=subprocess.check_output(['git','-C',str(clone),'rev-parse','HEAD'],text=True).strip()
  if actual!=a.commit or (clone/'.lake').exists():raise RuntimeError('The clone is not the requested fresh source tree')
  after=resource.getrusage(resource.RUSAGE_CHILDREN)
  receipt['clone_stage']={'wall_s':time.monotonic()-clock,'cpu_s':after.ru_utime+after.ru_stime-before.ru_utime-before.ru_stime,'max_single_rss_bytes':after.ru_maxrss*1024}
  if subprocess.run([sys.executable,'-c','import yaml'],env=env,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL).returncode:
   deps=work/'python-deps';run([sys.executable,'-m','pip','install','--disable-pip-version-check','--no-input','--no-cache-dir','--target',deps,'-r',verifier/'requirements.txt']);env['PYTHONPATH']=str(deps)
  remaining=a.budget-(time.monotonic()-start)
  receipt.update(status='verifying',clone=str(clone));save()
  cmd=[sys.executable,str(clone/'scripts/release_verify.py'),'--verifier',str(verifier),'--work',str(work/'verification'),
       '--budget',str(remaining),'--build-threads',str(a.build_threads)]
  with (work/'pipeline.log').open('w') as log:p=subprocess.run(cmd,cwd=clone,env=env,stdout=log,stderr=subprocess.STDOUT,timeout=max(1,remaining+15))
  child=work/'verification/receipt.json'
  if child.is_file():receipt['verification']=json.loads(child.read_text())
  receipt['exit_code']=p.returncode;receipt['status']='complete' if p.returncode==0 else 'incomplete';save()
  print(str(work/'receipt.json'));return p.returncode
 except Exception as e:
  receipt.update(status='incomplete',error=str(e));save();print(str(e),file=sys.stderr);print(str(work/'receipt.json'));return 1
if __name__=='__main__':raise SystemExit(main())
