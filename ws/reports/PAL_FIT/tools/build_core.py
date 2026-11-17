#!/usr/bin/env python3
"""Clean project-only source build, two workers, no Lake/dependency builds.

All project olean inputs are under candidate/.lake/build and start absent.
Pinned prebuilt dependency libraries are read-only. No shared .lake is modified.
Each worker has 15 GiB hard RLIMIT_AS, together 30 GiB; supervisor has
512 MiB kernel-enforced soft RLIMIT_AS, and affinity is inherited as 0-15.
A hard cap is used on workers; the supervisor retains its hard ceiling only
so that it can give subsequent workers their independently hard 15-GiB cap.
"""
import collections
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import resource
import signal
import subprocess
import sys
import time
sys.path.insert(0, str(Path(__file__).parent))
from limited import procstats, killgroup, GIB, CPUS

R=Path('/home/ubuntu/aklt/reports/PAL_FIT')
ROOT=R/'candidate'
OUT=ROOT/'.lake/build/lib/lean'
PREFIX=Path('/home/ubuntu/.elan/toolchains/leanprover--lean4---v4.35.0-rc2')
RESUME = os.environ.get('PAL_FIT_RESUME') == '1'
WORKERS = 1 if RESUME else 2
LIMIT_GIB = 31 if RESUME else 15
WORK=R/('clean-resume' if RESUME else 'clean-build')
WORK.mkdir(exist_ok=True)
lock=(R/'measurements/active.lock').open('w'); fcntl.flock(lock,fcntl.LOCK_EX)
os.sched_setaffinity(0,CPUS)
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,32*GIB))
if not RESUME:
 assert not any(OUT.rglob('*.olean')), 'Clean build requires absent project objects'
modules={'.'.join(p.relative_to(ROOT).with_suffix('').parts):p for p in ROOT.rglob('*.lean') if '.lake' not in p.parts}
# Header imports can span multiple modules on one line; all imports in this tree are line-oriented.
def imports(path):
 text=path.read_text()
 return {m for line in text.splitlines() if (mch:=re.match(r'\s*(?:public\s+)?(?:meta\s+)?import\s+(.+)',line)) for m in mch[1].split() if re.fullmatch(r'[\w.]+',m)}
deps={m:imports(p) & modules.keys() for m,p in modules.items()}
missing={m:sorted(i for i in imports(p) if (i.startswith('AKLT.') or i.startswith('CertData.')) and i not in modules) for m,p in modules.items()}
missing={m:d for m,d in missing.items() if d}
(R/'clean-dependencies.json').write_text(json.dumps(dict(modules=len(modules),missing=missing,deps={k:sorted(v) for k,v in deps.items()}),indent=2)+'\n')
if missing: raise SystemExit('Missing project source dependencies: '+repr(missing))
paths=(R/'lean-path.txt').read_text().strip().split(':')[1:]
env=os.environ.copy();env.update(LEAN_PATH=':'.join([str(OUT),*paths]),LEAN_NUM_THREADS='1',LEAN_ABORT_ON_PANIC='1',OMP_NUM_THREADS='1')
remaining=set(modules); done=set();failed={};blocked={};active={};records=[]
if RESUME:
 for line in (R/'clean-build/modules.jsonl').read_text().splitlines():
  row=json.loads(line)
  if row['exit_code']==0:
   obj=OUT/Path(*row['module'].split('.')).with_suffix('.olean')
   if obj.is_file(): done.add(row['module'])
 remaining-=done
start=time.monotonic();cpu=0;peakrss=0;peakvms=0;maxactive=0
samples=(WORK/'samples.jsonl').open('w');ledger=(WORK/'modules.jsonl').open('w');nextsample=start

def setup():
 os.setsid();os.sched_setaffinity(0,CPUS)
 resource.setrlimit(resource.RLIMIT_AS,(LIMIT_GIB*GIB,LIMIT_GIB*GIB))
 resource.setrlimit(resource.RLIMIT_CORE,(0,0))

def save(final=False):
 receipt=dict(started_utc=started_utc,wall_s=time.monotonic()-start,cpu_s=cpu,peak_worker_rss_sum_bytes=peakrss,peak_worker_vms_sum_bytes=peakvms,
  worker_hard_as_bytes=LIMIT_GIB*GIB,supervisor_soft_as_bytes=512*1024**2,total_reservation_bytes=WORKERS*LIMIT_GIB*GIB+512*1024**2,affinity=list(sorted(CPUS)),
  requested_modules=len(modules),passed=len(done),failed=failed,blocked=blocked,running=[x['module'] for x in active.values()],pending=len(remaining),
  max_active_workers=maxactive,fresh_project_objects=True,dependency_cache='existing pinned read-only Mathlib/dependency artifacts; fetching not measured',
  official_lake_build=False,cgroup_enforced=False,swap_limit_enforced=False,finished=final)
 (WORK/'result.json').write_text(json.dumps(receipt,indent=2)+'\n')
 return receipt
started_utc=time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime())
while remaining or active:
 for m in sorted(remaining):
  if deps[m] & (failed.keys() | blocked.keys()):
   blocked[m]=sorted(deps[m] & (failed.keys() | blocked.keys()));remaining.remove(m)
 for m in sorted(remaining):
  if len(active)>=WORKERS:break
  if deps[m] <= done:
   dest=WORK/m;dest.mkdir(exist_ok=True)
   output=OUT/Path(*m.split('.')).with_suffix('.olean');output.parent.mkdir(parents=True,exist_ok=True)
   argv=[str(PREFIX/'bin/lean'),'-j1','-DautoImplicit=false','-DrelaxedAutoImplicit=false','-o',str(output),str(modules[m])]
   log=(dest/'lean.log').open('wb')
   p=subprocess.Popen(argv,cwd=ROOT,env=env,stdout=log,stderr=subprocess.STDOUT,preexec_fn=setup)
   active[p.pid]=dict(module=m,process=p,argv=argv,start=time.monotonic(),log=log,peakrss=0,peakvms=0,maxthreads=0,timeout=False)
   remaining.remove(m);maxactive=max(maxactive,len(active))
 now=time.monotonic();totalrss=0;totalvms=0
 for pid,a in list(active.items()):
  waited,status,usage=os.wait4(pid,os.WNOHANG)
  if waited:
   rc=os.waitstatus_to_exitcode(status);a['process'].returncode=rc;a['log'].close()
   row=dict(module=a['module'],argv=a['argv'],exit_code=rc,wall_s=now-a['start'],cpu_s=usage.ru_utime+usage.ru_stime,peak_rss_bytes=max(a['peakrss'],usage.ru_maxrss*1024),peak_vms_bytes=a['peakvms'],max_threads=a['maxthreads'],timeout=a['timeout'])
   cpu+=row['cpu_s'];records.append(row);ledger.write(json.dumps(row)+'\n');ledger.flush()
   if rc==0:done.add(a['module'])
   else:failed[a['module']]=row
   del active[pid]
  else:
   stat=procstats(pid)
   if stat:
    totalrss+=stat['rss'];totalvms+=stat['vms'];a['peakrss']=max(a['peakrss'],stat['rss'],stat['hwm']);a['peakvms']=max(a['peakvms'],stat['vms']);a['maxthreads']=max(a['maxthreads'],stat['threads'])
    if stat['children'] or stat['cpus']!='0-15':
     a['timeout']='unexpected descendant or affinity';killgroup(pid)
   if now-a['start']>1200:
    a['timeout']=True;killgroup(pid)
 peakrss=max(peakrss,totalrss);peakvms=max(peakvms,totalvms)
 if now>=nextsample:
  samples.write(json.dumps(dict(elapsed_s=now-start,rss_bytes=totalrss,vms_bytes=totalvms,active=[a['module'] for a in active.values()],passed=len(done),failed=len(failed)))+'\n');samples.flush();save();nextsample=now+1
 if remaining and not active and not any(deps[m]<=done for m in remaining):
  for m in remaining:blocked[m]=sorted(deps[m]-done)
  remaining.clear()
 if now-start>17000:
  for a in active.values():killgroup(a['process'].pid)
  for m in remaining:blocked[m]=['campaign clean-build deadline']
  remaining.clear()
 time.sleep(.05)
receipt=save(True)
ledger.close();samples.close()
with (R/'report.md').open('a') as report:
 report.write('\nClean project build receipt (recorded immediately):\n\n```json\n'+json.dumps(receipt,indent=2)+'\n```\n')
print(json.dumps(receipt,indent=2))
