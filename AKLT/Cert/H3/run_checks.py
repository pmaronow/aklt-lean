#!/usr/bin/env python3
"""Fresh Lean processes, normal kernel checking, bounded memory and disk guards."""
import argparse, json, os, pathlib, resource, shutil, subprocess, time
ROOT = pathlib.Path(__file__).resolve().parents[3]
REPORT = pathlib.Path('/home/ubuntu/aklt/reports/CERT_H3')

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('modules', nargs='+')
    ap.add_argument('--timeout', type=int, default=600)
    ap.add_argument('--memory-gib', type=int, default=48)
    ap.add_argument('--profile', action='store_true')
    args = ap.parse_args()
    env = os.environ.copy()
    env['PATH'] = str(pathlib.Path.home()/'.elan/bin') + ':' + env.get('PATH','')
    env['LEAN_NUM_THREADS'] = '1'
    if not env.get('H3_LAKE_ENV'):
        env['H3_LAKE_ENV'] = '1'
        return subprocess.call(['lake','env','python3',__file__,*os.sys.argv[1:]], cwd=ROOT, env=env)
    # Lean selects the first top-level namespace directory. Present prebuilt
    # read-only dependencies and our own oleans under one scratch import root.
    lib = pathlib.Path('/home/ubuntu/aklt/scratch/CERT_H3/leanlib')
    ns = lib/'AKLT'; ns.mkdir(parents=True,exist_ok=True)
    prebuilt = pathlib.Path('/home/ubuntu/aklt/repo/.lake/build/lib/lean/AKLT')
    for dep in prebuilt.iterdir():
        if dep.name == 'Cert': continue
        dest = ns/dep.name
        if not dest.exists(): dest.symlink_to(dep,target_is_directory=dep.is_dir())
    (ns/'Cert').mkdir(exist_ok=True)
    if not (ns/'Cert/H3').exists(): (ns/'Cert/H3').symlink_to(ROOT/'CertData/H3/Kernel',target_is_directory=True)
    if not (lib/'CertData').exists(): (lib/'CertData').symlink_to(ROOT/'CertData',target_is_directory=True)
    env['LEAN_PATH'] = str(lib) + ':' + env.get('LEAN_PATH','')
    (REPORT/'logs').mkdir(parents=True, exist_ok=True)
    def limits():
        resource.setrlimit(resource.RLIMIT_CORE, (0,0))
        cap = args.memory_gib * 1024**3
        resource.setrlimit(resource.RLIMIT_AS, (cap, cap))
    for mod in args.modules:
        if shutil.disk_usage('/').free < 100 * 1024**3:
            raise SystemExit('ABORT: free disk below 100 GB')
        src = pathlib.Path(mod.replace('.','/')+'.lean')
        stem = mod.replace('.', '_') + ('_profile' if args.profile else '')
        log = REPORT/'logs'/f'{stem}.log'
        stats = REPORT/'logs'/f'{stem}.time'
        cmd = ['/usr/bin/time','-v','-o',str(stats),'timeout',str(args.timeout),
               'lean','-DautoImplicit=false','-DrelaxedAutoImplicit=false','-DElab.async=false','-o',str(src.with_suffix('.olean')),str(src)]
        if args.profile: cmd.insert(-1, '-Dprofiler=true')
        start = time.monotonic()
        with log.open('w') as f:
            p = subprocess.run(cmd, cwd=ROOT,env=env,stdout=f,stderr=subprocess.STDOUT,preexec_fn=limits)
        rec = dict(module=mod,profile=args.profile,command=cmd,exit=p.returncode,wall=time.monotonic()-start,
                   source_bytes=(ROOT/src).stat().st_size, log=str(log))
        txt = stats.read_text() if stats.exists() else ''
        for line in txt.splitlines():
            if 'Maximum resident set size (kbytes):' in line:
                rec['rss_kib']=int(line.split(':')[-1])
            if 'User time (seconds):' in line: rec['user_s']=float(line.split(':')[-1])
            if 'System time (seconds):' in line: rec['sys_s']=float(line.split(':')[-1])
        ole = ROOT/src.with_suffix('.olean')
        if p.returncode == 0 and ole.exists(): rec['olean_bytes']=ole.stat().st_size
        with (REPORT/'measurements.jsonl').open('a') as f: f.write(json.dumps(rec)+'\n')
        print(json.dumps(rec),flush=True)
        if p.returncode:
            print(log.read_text()[-15000:],flush=True)
            return p.returncode
    return 0
if __name__ == '__main__': raise SystemExit(main())
