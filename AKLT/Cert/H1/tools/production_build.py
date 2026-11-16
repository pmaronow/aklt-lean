#!/usr/bin/env python3
"""Dependency-aware, resumable production pilot; independent Lean processes.

Acceptance is always Lean kernel checking. Cache hashes only decide whether an
unchanged prior successful build can be reused; they are never proof premises.
"""
from __future__ import annotations
import argparse, concurrent.futures, fcntl, gzip, hashlib, json, os, re, resource, shutil, signal, subprocess, threading, time
from pathlib import Path

ROOT=Path(__file__).resolve().parents[4]
REPORT=Path('/home/ubuntu/aklt/reports/CERT_H1/phase2')
lock=threading.Lock();last_disk=0.;abort=threading.Event()
live_rss={}
peak_rss=0
_files={}
_sources={}
H3_DONE=Path('/home/ubuntu/aklt/flags/CERT_H3-p3.done')
_resource_phase=None
_resource_records=[]

def resource_limits():
    """The phase-3 lane allocation; leave physical memory for proof writers."""
    global _resource_phase
    phase='shared' if not H3_DONE.exists() else 'after_h3'
    if phase!=_resource_phase:
        available=int(re.search(r'^MemAvailable:\s*(\d+)',Path('/proc/meminfo').read_text(),re.M).group(1))*1024
        if phase=='after_h3':
            result=subprocess.run(['free','-g'],capture_output=True,text=True)
            print('RESOURCE CHECK\n'+result.stdout,flush=True)
        _resource_records.append(dict(phase=phase,time=time.time(),mem_available_bytes=available))
        _resource_phase=phase
    return (24,245_000_000_000) if phase=='shared' else (44,410_000_000_000)

def source_bytes(path):
    if path.exists():return path.read_bytes()
    with gzip.open(str(path)+'.gz','rb') as f:return f.read()

def source_digest(path):return hashlib.sha256(source_bytes(path)).hexdigest()

def compact_source(path):
    if not path.is_relative_to(ROOT/'CertData/H1/Generated') or not path.exists():return
    payload=path.read_bytes();target=Path(str(path)+'.gz');temp=Path(str(target)+'.tmp')
    temp.write_bytes(gzip.compress(payload,compresslevel=9,mtime=0));temp.replace(target);path.unlink()

def file_digest(path):
    st=path.stat();stamp=(st.st_mtime_ns,st.st_size)
    key=str(path);cached=_files.get(key)
    if cached and cached[0]==stamp:return cached[1]
    value=sha(path);_files[key]=(stamp,value);return value

def library_fingerprint(module,seen=None):
    """Source and artifact closure, including imports hidden by a data module.

    Mathlib/Lean are pinned dependencies and never rebuilt by this task. AKLT
    dependency sources/artifacts are read from the supplied prebuilt checkout.
    """
    seen=set() if seen is None else seen
    if module in seen:return ''
    seen.add(module)
    owned=module.startswith('AKLT.Cert.H1.')
    base=ROOT if owned else Path('/home/ubuntu/aklt/repo')
    source=base/(module.replace('.','/')+'.lean')
    artifact=source.with_suffix('.olean') if owned else base/'.lake/build/lib/lean'/(module.replace('.','/')+'.olean')
    if not source.exists() or not artifact.exists():raise FileNotFoundError('run production_bootstrap first: '+module)
    source_sha=file_digest(source)
    cache=_sources.get(str(source))
    if not cache or cache[0]!=source_sha:
        imports=re.findall(r'^import (AKLT\.[\w.]+)',source.read_text(),re.M)
        _sources[str(source)]=(source_sha,imports)
    else:imports=cache[1]
    parts=[module,source_sha,file_digest(artifact)]
    for companion in sorted(artifact.parent.glob(artifact.name+'.*')):
        if companion.is_file():parts.append(file_digest(companion))
    parts += [library_fingerprint(m,seen) for m in imports]
    return hashlib.sha256(''.join(parts).encode()).hexdigest()

def build_key(source,dependencies):
    payload=source_bytes(source)
    imports=re.findall(r'^import (AKLT\.[\w.]+)',payload.decode(),re.M)
    core=''.join(library_fingerprint(m) for m in imports)
    pins=''.join(file_digest(ROOT/n) for n in ['lean-toolchain','lake-manifest.json'] if (ROOT/n).exists())
    material='h1-key-v2'+hashlib.sha256(payload).hexdigest()+pins+core
    material+=''.join(x['key']+x['artifact_sha256'] for x in dependencies)
    return hashlib.sha256(material.encode()).hexdigest(),core

def group_rss(pid):
    """Count the process tree, including Lean below Lake and GNU time."""
    try:
        status=Path(f'/proc/{pid}/status').read_text()
        m=re.search(r'^VmRSS:\s*(\d+) kB',status,re.M)
        own=int(m.group(1))*1024 if m else 0
        children=Path(f'/proc/{pid}/task/{pid}/children').read_text().split()
        return own+sum(group_rss(int(c)) for c in children)
    except (FileNotFoundError,ProcessLookupError):return 0

def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()

def guard():
    global last_disk
    if shutil.disk_usage('/').free<100*2**30:
        abort.set();raise RuntimeError('ABORT: / free disk below 100 GiB')
    available=int(re.search(r'^MemAvailable:\s*(\d+)',Path('/proc/meminfo').read_text(),re.M).group(1))*1024
    if available<40_000_000_000:
        abort.set();raise MemoryError('ABORT: physical memory available below 40 GB')
    with lock:
        if time.monotonic()-last_disk>30:
            total=0
            for base in [ROOT/'AKLT/Cert/H1',ROOT/'CertData',Path('/home/ubuntu/aklt/reports/CERT_H1')]:
                for path in base.rglob('*'):
                    if path.is_file() and not path.is_symlink():
                        try:st=path.stat()
                        except FileNotFoundError:continue  # another worker atomically replaced its state
                        total+=max(st.st_size,st.st_blocks*512)
            if total>40_000_000_000:
                abort.set();raise RuntimeError('ABORT: 40 GB task budget exceeded')
            last_disk=time.monotonic()

def metrics(path):
    t=path.read_text()
    def number(pattern):
        m=re.search(pattern,t);return float(m.group(1)) if m else None
    return dict(user_seconds=number(r'User time \(seconds\): ([0-9.]+)'),
                system_seconds=number(r'System time \(seconds\): ([0-9.]+)'),
                max_rss_kib=number(r'Maximum resident set size \(kbytes\): (\d+)'),
                axiom_lines=[x.strip() for x in t.splitlines() if 'depends on axioms' in x or 'does not depend on any axioms' in x])

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('manifest',type=Path)
    ap.add_argument('--jobs',type=int,default=24)
    ap.add_argument('--cap-gib',type=int,default=11)
    ap.add_argument('--seconds',type=int,default=1200)
    ap.add_argument('--kinds',nargs='+')
    ap.add_argument('--force',action='store_true')
    ap.add_argument('--force-kinds',nargs='+',default=[],help='recheck selected stages while replaying their unchanged dependencies')
    ap.add_argument('--jobs-file',type=Path,help='optional live concurrency setting (1..44; allocation is clamped by the H3 flag)')
    ap.add_argument('--compact-sources',action='store_true',help='gzip checked generated sources and retain all oleans')
    ap.add_argument('--report-dir',type=Path,help='isolated run logs, state and receipts')
    args=ap.parse_args()
    if not 1<=args.jobs<=44:ap.error('at most 44 processes, and only after H3 completion')
    global REPORT
    if args.report_dir:REPORT=args.report_dir
    REPORT.mkdir(parents=True,exist_ok=True);logs=REPORT/'logs';logs.mkdir(exist_ok=True)
    cache=ROOT/'.lake/build/lib/lean/CertData'
    if not cache.exists():cache.symlink_to(ROOT/'CertData',target_is_directory=True)
    plan=json.loads(args.manifest.read_text());alljobs={j['module']:j for j in plan['jobs']}
    wanted=set(alljobs)
    if args.kinds:
        wanted={m for m,j in alljobs.items() if j['kind'] in args.kinds}
        def add_deps(m):
            for d in alljobs[m]['deps']:
                if d not in wanted:wanted.add(d);add_deps(d)
        for m in list(wanted):add_deps(m)
    jobs={m:alljobs[m] for m in wanted}
    statepath=REPORT/('state-'+args.manifest.stem+'.json')
    seed=statepath if statepath.exists() else REPORT/'build-state.json'
    state=json.loads(seed.read_text()) if seed.exists() else {}
    events=REPORT/'events.jsonl'
    # Replay the successful-build journal, including work from other frontiers.
    # Each candidate is still checked against source/dependencies and artifact.
    if events.exists():
        for line in events.read_text().splitlines():
            try:record=json.loads(line)
            except json.JSONDecodeError:continue  # interrupted final append
            if record.get('exit')==0 and record.get('artifact_sha256'):
                state[record['module']]=record
    env=os.environ.copy();env['PATH']=str(Path.home()/'.elan/bin')+':'+env['PATH']
    env['LEAN_PATH']=str(ROOT/'.lake/build/lib/lean');env['LEAN_NUM_THREADS']='1'
    def run(m):
        global peak_rss
        guard();j=jobs[m];src=ROOT/(m.replace('.','/')+'.lean');obj=src.with_suffix('.olean')
        cap_gib=j.get('cap_gib',args.cap_gib)
        if not (src.is_relative_to(ROOT/'AKLT/Cert/H1') or src.is_relative_to(ROOT/'CertData')):
            raise ValueError('source outside the assigned certificate roots')
        # Cross-runner lock: frontier replay never runs two Lean writers for
        # the same module, even when their manifests overlap.
        lockdir=REPORT/'module-locks';lockdir.mkdir(exist_ok=True)
        module_lock=(lockdir/(m+'.lock')).open('a')
        with module_lock:
            fcntl.flock(module_lock,fcntl.LOCK_EX)
            key,core=build_key(src,[state[d] for d in j['deps']])
            if obj.exists() and (m not in state or state[m].get('key')!=key) and events.exists():
                for line in reversed(events.read_text().splitlines()):
                    try:candidate=json.loads(line)
                    except json.JSONDecodeError:continue
                    if candidate.get('module')==m and candidate.get('exit')==0:
                        state[m]=candidate;break
            if not args.force and j['kind'] not in args.force_kinds and m in state and state[m].get('key')==key and obj.exists() and sha(obj)==state[m].get('artifact_sha256'):
                if args.compact_sources:compact_source(src)
                return m,dict(state[m],replayed=True)
            if not src.exists():src.write_bytes(source_bytes(src))
            log=logs/(m.replace('.','__')+'.log')
            cmd=['/usr/bin/time','-v','/usr/bin/prlimit',f'--as={max(64,2*cap_gib)*2**30}',
                 '--','lake','env','lean','-DElab.async=false','-DautoImplicit=false',
                 '-DrelaxedAutoImplicit=false','--profile','-o',str(obj),str(src)]
            # Prebuilt Mathlib mappings need much more virtual space than RSS.
            # Enforce physical-memory limits separately, rather than starving mmap.
            begin=time.monotonic()
            with log.open('w') as f:
                f.write('COMMAND: '+repr(cmd)+'\n');f.flush()
                p=subprocess.Popen(cmd,cwd=ROOT,env=env,stdout=f,stderr=subprocess.STDOUT,start_new_session=True)
                try:
                    while p.poll() is None:
                        guard()
                        rss=group_rss(p.pid)
                        with lock:
                            live_rss[m]=rss
                            peak_rss=max(peak_rss,sum(live_rss.values()))
                            over_total=sum(live_rss.values())>resource_limits()[1]
                        if rss>cap_gib*2**30 or over_total:
                            abort.set();raise MemoryError('RSS limit '+m)
                        if abort.is_set() or time.monotonic()-begin>args.seconds:raise TimeoutError(m)
                        time.sleep(.25)
                except BaseException:
                    abort.set()
                    os.killpg(p.pid,signal.SIGKILL);p.wait();raise
                finally:
                    with lock:live_rss.pop(m,None)
            result=dict(module=m,kind=j['kind'],pid=j.get('pid'),block=j.get('block'),exit=p.returncode,
                        wall_seconds=round(time.monotonic()-begin,4),log=str(log),key=key,key_version=2,
                        source_sha256=source_digest(src),library_closure=core,replayed=False,manifest=str(args.manifest),cap_gib=cap_gib,**metrics(log))
            if p.returncode:
                print(json.dumps(result),flush=True);print(log.read_text()[-6000:],flush=True)
                abort.set();raise RuntimeError('Lean failed '+m)
            if result['max_rss_kib'] and result['max_rss_kib']>cap_gib*2**20:
                abort.set();raise MemoryError('GNU time peak RSS exceeds per-module cap '+m)
            axiom_sets=re.findall(r'depends on axioms:\s*\[([^\]]*)\]',log.read_text(),re.S)
            used={v.strip() for a in axiom_sets for v in a.split(',') if v.strip()}
            if not used <= {'propext','Classical.choice','Quot.sound'}:raise RuntimeError('forbidden dependency '+m+': '+repr(used))
            result['axioms']=sorted(used)
            result['artifact_sha256']=sha(obj)
            with lock:
                with events.open('a') as f:
                    fcntl.flock(f,fcntl.LOCK_EX)
                    f.write(json.dumps(result,sort_keys=True)+'\n');f.flush()
                    fcntl.flock(f,fcntl.LOCK_UN)
            if args.compact_sources:compact_source(src)
            return m,result
    begin=time.monotonic();done=set();pending=set(jobs);running={};completed=0;replayed=0
    max_running=0
    with concurrent.futures.ThreadPoolExecutor(max_workers=44) as pool:
        while pending or running:
            concurrency=args.jobs
            if args.jobs_file and args.jobs_file.exists():
                concurrency=int(args.jobs_file.read_text().strip())
                if not 1<=concurrency<=44:raise ValueError('jobs file must specify 1..44')
            allowed,memory_limit=resource_limits()
            concurrency=min(concurrency,allowed)
            ready=sorted(m for m in pending if all(d in done for d in jobs[m]['deps']))
            # Start long numerical jobs before small assemblies after their inputs exist.
            ready.sort(key=lambda m:(jobs[m]['kind'] not in ['constructor_rows','gram_rows'], -jobs[m].get('n',0),m))
            reserved=sum(jobs[m].get('cap_gib',args.cap_gib)*2**30 for m in running.values())
            # A freshly started Lean process has not reached its reserved RSS.
            # Keep room for that future growth as well as 40 GB for other users.
            with lock:
                outstanding=sum(max(0,jobs[m].get('cap_gib',args.cap_gib)*2**30-live_rss.get(m,0)) for m in running.values())
            for m in ready:
                if len(running)>=concurrency:break
                reservation=jobs[m].get('cap_gib',args.cap_gib)*2**30
                if reserved+reservation>memory_limit:continue
                available=int(re.search(r'^MemAvailable:\s*(\d+)',Path('/proc/meminfo').read_text(),re.M).group(1))*1024
                if available-outstanding-reservation<40_000_000_000:continue
                pending.remove(m);running[pool.submit(run,m)]=m;reserved+=reservation;outstanding+=reservation
            max_running=max(max_running,len(running))
            if not running:
                if not ready:raise RuntimeError('cycle or missing dependency')
                guard();time.sleep(2);continue
            finished,_=concurrent.futures.wait(running,timeout=2,return_when=concurrent.futures.FIRST_COMPLETED)
            for future in finished:
                m,result=future.result();del running[future];state[m]=result;done.add(m)
                completed+=1;replayed+=int(result['replayed'])
                tmp=statepath.with_suffix('.tmp');tmp.write_text(json.dumps(state,sort_keys=True));tmp.replace(statepath)
                if completed%20==0 or not pending and not running:
                    print(json.dumps(dict(completed=completed,total=len(jobs),replayed=replayed,running=len(running),wall_seconds=round(time.monotonic()-begin,1))),flush=True)
    runsummary=dict(manifest=str(args.manifest),modules=len(jobs),replayed=replayed,wall_seconds=time.monotonic()-begin,jobs=args.jobs,max_concurrent_jobs=max_running,cap_gib=args.cap_gib,peak_sampled_aggregate_rss_bytes=peak_rss,completed_at=time.time(),compact_sources=args.compact_sources,resource_phases=_resource_records)
    (REPORT/('run-'+args.manifest.stem+'.json')).write_text(json.dumps(runsummary,indent=2)+'\n');print(json.dumps(runsummary),flush=True)

if __name__=='__main__':main()
