from pathlib import Path
import subprocess,os,time,json,re,sys,hashlib
from concurrent.futures import ThreadPoolExecutor,wait,FIRST_COMPLETED
root=Path('/home/ubuntu/aklt/wt/BP_REC')
report=Path('/home/ubuntu/aklt/reports/BP_REC')
lib=report/'adaptation-olean';lib.mkdir(exist_ok=True)
mods={}
def add(m):
    if m in mods:return
    p=root/(m.replace('.','/')+'.lean')
    if not p.exists():raise RuntimeError('Missing local dependency '+m)
    mods[m]=p
    for dep in re.findall(r'^import (\S+)',p.read_text(),re.M):
        if dep.startswith('AKLT.'):add(dep)
for target in sys.argv[1:] or ['AKLT.Blueprint.Rec.AllV2']:add(target)
needs={m:set(re.findall(r'^import (\S+)',p.read_text(),re.M))&mods.keys() for m,p in mods.items()}
cachefile=report/'adaptation-build-cache.json'
cache=json.loads(cachefile.read_text()) if cachefile.exists() else {}
keys={}
def key(m):
    if m not in keys:
        keys[m]=hashlib.sha256((mods[m].read_text()+''.join(key(d) for d in sorted(needs[m]))).encode()).hexdigest()
    return keys[m]
for m in mods:key(m)
done={m for m in mods if cache.get(m)==keys[m] and (lib/(m.replace('.','/')+'.olean')).exists()}
pending=set(mods)-done;running={};rows=[]
env=os.environ.copy();env['LEAN_PATH']=str(lib)+':'+env.get('LEAN_PATH','')
def run(m):
    out=lib/(m.replace('.','/')+'.olean');out.parent.mkdir(parents=True,exist_ok=True)
    cmd=['lean','-DautoImplicit=false','-DrelaxedAutoImplicit=false','-o',str(out),str(mods[m].relative_to(root))]
    t=time.monotonic()
    r=subprocess.run(cmd,cwd=root,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    logfile=report/('adaptation-'+m+'.log');logfile.write_text(r.stdout)
    return dict(module=m,exit=r.returncode,seconds=round(time.monotonic()-t,2),log=str(logfile),command=cmd)
start=time.monotonic();failed=False
with ThreadPoolExecutor(max_workers=2) as pool:
    while pending or running:
        for m in sorted(pending):
            if len(running)>=2:break
            if needs[m]<=done:
                running[pool.submit(run,m)]=m;pending.remove(m)
        if not running:
            if pending:raise RuntimeError('Dependency cycle '+repr(pending))
            break
        ready,_=wait(running,return_when=FIRST_COMPLETED)
        for future in ready:
            m=running.pop(future);row=future.result();rows.append(row)
            print(m,'PASS' if row['exit']==0 else 'FAIL',row['seconds'],'s',flush=True)
            if row['exit']:
                print(Path(row['log']).read_text()[-11000:],flush=True);failed=True
            else:done.add(m);cache[m]=keys[m]
        if failed:
            for future,m in list(running.items()):
                row=future.result();rows.append(row)
                if row['exit']==0:cache[m]=keys[m]
            break
cachefile.write_text(json.dumps(cache,indent=2)+'\n')
(report/'adaptation-build.json').write_text(json.dumps({'wall_seconds':round(time.monotonic()-start,2),'parallel_limit':2,'targets':sys.argv[1:],'results':rows,'cached_count':len(mods)-len(rows)},indent=2)+'\n')
raise SystemExit(1 if failed else 0)
