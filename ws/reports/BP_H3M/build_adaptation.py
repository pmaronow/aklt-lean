"""Sequential olean-only build; never builds Mathlib or emits C for supplied literals."""
from pathlib import Path
import hashlib,json,os,re,subprocess,sys,time
root=Path('/home/ubuntu/aklt/wt/BP_H3M')
report=Path('/home/ubuntu/aklt/reports/BP_H3M')
lib=report/'adaptation-olean';lib.mkdir(exist_ok=True)
logs=report/'adaptation-build-logs';logs.mkdir(exist_ok=True)
statefile=report/'adaptation-build-state.json'
state=json.loads(statefile.read_text()) if statefile.exists() else {}
targets=sys.argv[1:] or ['AKLT.Blueprint.H3.NodesV2','AKLT.Blueprint.Top.Assembly']
mods={};needs={};order=[];active=set()
def visit(m):
    if m in mods:return
    if m in active:raise RuntimeError('Import cycle: '+m)
    active.add(m)
    p=root/(m.replace('.','/')+'.lean')
    src=p.read_text();deps=[x for x in re.findall(r'(?m)^import (\S+)',src) if x.startswith('AKLT.')]
    for d in deps:visit(d)
    active.remove(m);mods[m]=p;needs[m]=deps;order.append(m)
for m in targets:visit(m)
env=os.environ.copy();env['LEAN_PATH']=str(lib)+':'+env.get('LEAN_PATH','')
rows=[];sigs={};start=time.monotonic()
for m in order:
    p=mods[m]
    sig=hashlib.sha256(p.read_bytes()+''.join(sigs[d] for d in needs[m]).encode()).hexdigest();sigs[m]=sig
    out=lib/(m.replace('.','/')+'.olean')
    if state.get(m,{}).get('signature')==sig and out.exists():continue
    out.parent.mkdir(parents=True,exist_ok=True)
    cmd=['lean','-DautoImplicit=false','-DrelaxedAutoImplicit=false','-o',str(out),str(p.relative_to(root))]
    t=time.monotonic();r=subprocess.run(cmd,cwd=root,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    seconds=round(time.monotonic()-t,2)
    log=logs/(m+'.log');log.write_text(r.stdout)
    row=dict(module=m,exit_code=r.returncode,seconds=seconds,log=str(log),command=cmd)
    rows.append(row);print(m,'PASS' if not r.returncode else 'FAIL',seconds,'s',flush=True)
    if r.returncode:
        print(r.stdout[-15000:],flush=True)
        (report/'adaptation-build-last.json').write_text(json.dumps(dict(parallel_limit=1,results=rows,wall_seconds=round(time.monotonic()-start,2)),indent=2)+'\n')
        sys.exit(r.returncode)
    state[m]=dict(signature=sig,seconds=seconds,log=str(log))
    statefile.write_text(json.dumps(state,indent=2)+'\n')
(report/'adaptation-build-last.json').write_text(json.dumps(dict(parallel_limit=1,targets=targets,results=rows,wall_seconds=round(time.monotonic()-start,2)),indent=2)+'\n')
print('BUILD COMPLETE;',len(rows),'modules compiled;',round(time.monotonic()-start,2),'s; parallel limit 1',flush=True)
