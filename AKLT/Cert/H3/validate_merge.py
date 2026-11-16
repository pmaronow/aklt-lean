#!/usr/bin/env python3
"""Build just the merge-set import closure from frozen main source, no data/check modules."""
from pathlib import Path
import concurrent.futures,hashlib,json,os,re,shutil,subprocess,sys,time
ROOT=Path(__file__).resolve().parents[3]
REPORT=Path('/home/ubuntu/aklt/reports/CERT_H3/phase3')
DEST=Path('/home/ubuntu/aklt/scratch/CERT_H3/clean-merge')
def main():
 env=os.environ.copy();env['PATH']=str(Path.home()/'.elan/bin')+':'+env.get('PATH','')
 revision=json.load(open(REPORT/'statement-main-check.json'))['main'];sourcefiles=(REPORT.parent/'merge-set.txt').read_text().splitlines()
 DEST.mkdir(parents=True,exist_ok=True)
 for name in sourcefiles:
  p=ROOT/name;q=DEST/name;q.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,q)
 for name in ['lean-toolchain','lake-manifest.json']:
  q=DEST/name;q.write_bytes(subprocess.check_output(['git','show',revision+':'+name],cwd=ROOT))
 (DEST/'.lake').mkdir(exist_ok=True)
 if not (DEST/'.lake/packages').exists():(DEST/'.lake/packages').symlink_to((ROOT/'.lake/packages').resolve(),target_is_directory=True)
 modules={};imports={}
 def visit(mod):
  if not(mod.startswith('AKLT.') or mod.startswith('CertData.')):return
  if mod in modules:return
  name=mod.replace('.','/')+'.lean';p=DEST/name
  if name not in sourcefiles:
   data=subprocess.check_output(['git','show',revision+':'+name],cwd=ROOT);p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data)
  s=p.read_text();modules[mod]=p
  deps=[]
  for line in s.splitlines():
   m=re.match(r'^(?:(?:public|private) )?import (.+)$',line)
   if m:
    for dep in m[1].split():
     if dep.startswith(('AKLT.','CertData.')):deps.append(dep);visit(dep)
  imports[mod]=deps
 visit('CertData.H3.Core')
 # A merge-set audit uses no generated data and checks every writer leaf is closed.
 rows=json.load(open(REPORT.parent/'leaves-open.json'));p=DEST/'CertData/H3/MergeAudit.lean'
 p.write_text('import CertData.H3.Core\n'+''.join('#check ('+x['lean_name']+' : Prop)\n' for x in rows))
 modules['CertData.H3.MergeAudit']=p;imports['CertData.H3.MergeAudit']=['CertData.H3.Core']
 # The only external build environment is the already built Mathlib package.
 raw=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=DEST,env=env,text=True).strip()
 lib=DEST/'.lake/build/lib/lean';lib.mkdir(parents=True,exist_ok=True);env['LEAN_PATH']=str(lib)+':'+raw;env['LEAN_NUM_THREADS']='1'
 done=set();pending=set(modules);running={};results=[];start=time.monotonic();(REPORT/'clean-logs').mkdir(exist_ok=True)
 def run(mod):
  src=modules[mod];ole=lib/(mod.replace('.','/')+'.olean');ole.parent.mkdir(parents=True,exist_ok=True)
  log=REPORT/'clean-logs'/(mod.replace('.','_')+'.log');stats=log.with_suffix('.time');t=time.monotonic()
  with log.open('w') as f:
   code=subprocess.call(['/usr/bin/time','-v','-o',str(stats),'timeout','600','lean','-DautoImplicit=false','-DrelaxedAutoImplicit=false','-DElab.async=false','-o',str(ole),str(src.relative_to(DEST))],cwd=DEST,env=env,stdout=f,stderr=subprocess.STDOUT)
  r=dict(module=mod,exit=code,wall=time.monotonic()-t,log=str(log),source_sha256=hashlib.file_digest(src.open('rb'),'sha256').hexdigest())
  for line in stats.read_text().splitlines():
   if 'Maximum resident set size' in line:r['rss_kib']=int(line.split(':')[-1])
   if 'User time (seconds)' in line:r['user_s']=float(line.split(':')[-1])
   if 'System time (seconds)' in line:r['sys_s']=float(line.split(':')[-1])
  if code:print(log.read_text()[-6000:],flush=True)
  return r
 with concurrent.futures.ThreadPoolExecutor(max_workers=3) as pool:
  while pending or running:
   for mod in sorted(pending):
    if len(running)>=3:break
    if all(x in done for x in imports[mod]):running[pool.submit(run,mod)]=mod;pending.remove(mod)
   if not running:raise RuntimeError('blocked import closure')
   complete,_=concurrent.futures.wait(running,return_when=concurrent.futures.FIRST_COMPLETED)
   for fut in complete:
    mod=running.pop(fut);res=fut.result();results.append(res)
    if res['exit']:raise RuntimeError('clean merge build failed: '+mod)
    done.add(mod)
   print(json.dumps(dict(done=len(done),total=len(modules),wall=time.monotonic()-start)),flush=True)
 receipt=dict(main=revision,root='CertData.H3.Core',optional_target='CertData',workers=3,wall=time.monotonic()-start,closed_leaves=len(rows),all_exit_zero=all(x['exit']==0 for x in results),modules=results,
  merge_sources=[dict(path=n,sha256=hashlib.file_digest((ROOT/n).open('rb'),'sha256').hexdigest()) for n in sourcefiles],
  added_ordinary_AKLT_lean_sources=[n for n in sourcefiles if n.startswith('AKLT/') and n.endswith('.lean')])
 (REPORT/'clean-merge-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps({k:v for k,v in receipt.items() if k not in ['modules','merge_sources']},indent=2))
if __name__=='__main__':main()
