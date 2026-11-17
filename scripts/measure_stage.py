#!/usr/bin/env python3
"""Time a stage with 16-CPU affinity and process-tree RSS telemetry.
External cgroup limits, when present, remain the authoritative memory limits.
"""
import argparse,datetime,json,os,resource,shutil,signal,subprocess,time
from pathlib import Path

def stat(pid):
 try:
  root=Path('/proc')/str(pid);d={}
  for line in (root/'status').read_text().splitlines():
   k,_,v=line.partition(':');d[k]=v.strip()
  raw=(root/'stat').read_text();f=raw[raw.rfind(')')+2:].split();children=set()
  for task in (root/'task').iterdir():
   try:children.update(int(x) for x in (task/'children').read_text().split())
   except (FileNotFoundError,ProcessLookupError):pass
  cmd=(root/'cmdline').read_bytes().split(b'\0');exe=os.fsdecode(cmd[0]) if cmd and cmd[0] else ''
  return dict(pid=pid,rss=int(d.get('VmRSS','0 kB').split()[0])*1024,vms=int(d.get('VmSize','0 kB').split()[0])*1024,
   hwm=int(d.get('VmHWM','0 kB').split()[0])*1024,threads=int(d.get('Threads','0')),cpu_ticks=int(f[11])+int(f[12]),
   start_ticks=int(f[19]),children=sorted(children),exe=exe,args=[os.fsdecode(x) for x in cmd if x],cpus=d.get('Cpus_allowed_list',''))
 except (OSError,ProcessLookupError):return None

def exceeds_affinity(pid,allowed):
 try:return bool(os.sched_getaffinity(pid)-set(allowed))
 except ProcessLookupError:return False

def tree(pid):
 todo=[pid];seen=set();rows=[]
 while todo:
  n=todo.pop()
  if n in seen:continue
  seen.add(n);s=stat(n)
  if s:rows.append(s);todo.extend(s['children'])
 return rows

def kill(pid,rows):
 for r in reversed(rows):
  try:os.kill(r['pid'],signal.SIGKILL)
  except ProcessLookupError:pass
 try:os.killpg(pid,signal.SIGKILL)
 except ProcessLookupError:pass

def cgroups():
 result={'authenticated_palomar_telemetry':False}
 try:
  entry=next(x for x in Path('/proc/self/cgroup').read_text().splitlines() if x.startswith('0::'))[3:]
  d=Path('/sys/fs/cgroup')/entry.lstrip('/');result['path']=str(d);result['limits']={}
  for key in ['cpu.max','memory.max','memory.high','memory.swap.max']:
   try:result['limits'][key]=(d/key).read_text().strip()
   except OSError:pass
  for key in ['cpu.stat','memory.peak','memory.events']:
   try:result[key]=(d/key).read_text().strip()
   except OSError:pass
 except (OSError,StopIteration):pass
 return result

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--stage',required=True);ap.add_argument('--out',type=Path,required=True)
 ap.add_argument('--cwd',type=Path,default=Path.cwd());ap.add_argument('--timeout',type=float,default=19800)
 ap.add_argument('--rss-cap-gb',type=float,default=260);ap.add_argument('--max-lean',type=int,default=48)
 ap.add_argument('--campaign-report',type=Path);ap.add_argument('command',nargs=argparse.REMAINDER);a=ap.parse_args()
 cpus=sorted(os.sched_getaffinity(0))[:16];os.sched_setaffinity(0,cpus);assert len(cpus)==16
 cmd=a.command[1:] if a.command and a.command[0]=='--' else a.command
 assert cmd;a.out.mkdir(parents=True,exist_ok=True)
 cg_before=cgroups();started=datetime.datetime.now(datetime.timezone.utc).isoformat();clock=time.monotonic();seen_cpu={};peak=0;peak_single=0;peak_vms=0;peak_threads=0;peak_processes=0;peak_lean=0;limit=None
 def setup():
  os.sched_setaffinity(0,cpus);resource.setrlimit(resource.RLIMIT_CORE,(0,0));resource.setrlimit(resource.RLIMIT_AS,(240*1024**3,)*2)
 with (a.out/'stdout.log').open('wb') as out,(a.out/'stderr.log').open('wb') as err,(a.out/'samples.jsonl').open('w') as log:
  proc=subprocess.Popen(cmd,cwd=a.cwd,stdout=out,stderr=err,start_new_session=True,preexec_fn=setup)
  next_sample=clock
  while True:
   pid,status,usage=os.wait4(proc.pid,os.WNOHANG)
   if pid:proc.returncode=os.waitstatus_to_exitcode(status);break
   rows=tree(proc.pid);now=time.monotonic();rss=sum(x['rss'] for x in rows);vms=sum(x['vms'] for x in rows);threads=sum(x['threads'] for x in rows)
   nlean=sum(Path(x['exe']).name in ['lean','lean.exe'] for x in rows)
   peak=max(peak,rss);peak_single=max(peak_single,max((x['hwm'] for x in rows),default=0));peak_vms=max(peak_vms,vms)
   peak_threads=max(peak_threads,threads);peak_processes=max(peak_processes,len(rows));peak_lean=max(peak_lean,nlean)
   for x in rows:seen_cpu[(x['pid'],x['start_ticks'])]=max(seen_cpu.get((x['pid'],x['start_ticks']),0),x['cpu_ticks'])
   if now>=next_sample:
    log.write(json.dumps(dict(elapsed_s=now-clock,rss=rss,vms=vms,threads=threads,lean_processes=nlean,processes=rows))+'\n');log.flush();next_sample=now+1
   if any(exceeds_affinity(x['pid'],cpus) for x in rows):limit='affinity_violation'
   elif now-clock>a.timeout:limit='wall_timeout'
   elif rss>a.rss_cap_gb*10**9:limit='diagnostic_rss_cap'
   elif shutil.disk_usage(a.cwd).free<20*1024**3:limit='workspace_free_below_20_GiB'
   elif nlean>a.max_lean:limit='lean_process_cap'
   if limit:kill(proc.pid,rows)
   time.sleep(.10)
 result=dict(stage=a.stage,started_utc=started,command=cmd,cwd=str(a.cwd),exit_code=proc.returncode,wall_s=time.monotonic()-clock,
  user_s=usage.ru_utime,system_s=usage.ru_stime,cpu_s=usage.ru_utime+usage.ru_stime,
  sampled_tree_cpu_s=sum(seen_cpu.values())/os.sysconf('SC_CLK_TCK'),peak_tree_rss_bytes=peak,
  peak_single_rss_bytes=max(peak_single,usage.ru_maxrss*1024),peak_tree_vms_bytes=peak_vms,peak_threads=peak_threads,
  peak_processes=peak_processes,peak_lean_processes=peak_lean,affinity_cpus=cpus,timeout_s=a.timeout,limit=limit,rss_cap_gb=a.rss_cap_gb,
  virtual_address_limit_per_process_bytes=240*1024**3,cgroup=cgroups(),memory_note='Sampled RSS sum may double-count shared pages; not cgroup RAM/page-cache accounting; wait4 may omit namespace descendants.')
 result['wait4_cpu_s']=result['cpu_s']
 result['cpu_s']=max(result['cpu_s'],result['sampled_tree_cpu_s'])
 result['cpu_method']='wait4 cumulative' if result['wait4_cpu_s']>=result['sampled_tree_cpu_s'] else 'sampled process-tree CPU; approximate because namespace PID 1 does not forward rusage'
 result['cgroup_before']=cg_before
 (a.out/'result.json').write_text(json.dumps(result,indent=2)+'\n')
 if a.campaign_report:
  with a.campaign_report.open('a') as f:f.write(f"\nRelease stage `{a.stage}`: wall {result['wall_s']:.3f} s, CPU {result['cpu_s']:.3f} s, peak tree RSS {peak/2**30:.3f} GiB, exit {proc.returncode}, limit {limit}. Receipt: `{a.out/'result.json'}`.\n")
 print(json.dumps(result,indent=2));return 0 if proc.returncode==0 and not limit else 1
if __name__=='__main__':raise SystemExit(main())
