import os, pathlib, subprocess, time, sys, json
root=pathlib.Path('/home/ubuntu/aklt/wt/BP_H1M')
report=pathlib.Path('/home/ubuntu/aklt/reports/BP_H1M')
env=os.environ.copy(); env['PATH']=str(pathlib.Path.home()/'.elan/bin')+':'+env['PATH']
seen=set(); order=[]
def visit(module):
    if module in seen: return
    seen.add(module)
    path=root/(module.replace('.', '/')+'.lean')
    if not path.exists(): return
    for line in path.read_text().splitlines():
        if line.startswith('import '):
            for dep in line[7:].split():
                if dep.startswith('AKLT.'): visit(dep)
    order.append(module)
for m in sys.argv[1:]: visit(m)
rows=[]
with (report/'build.log').open('w') as log:
    for module in order:
        src=root/(module.replace('.', '/')+'.lean')
        target=root/'.lake/build/lib/lean'/(module.replace('.', '/')+'.olean')
        target.parent.mkdir(parents=True,exist_ok=True)
        start=time.monotonic()
        p=subprocess.run(['lake','env','lean','-o',str(target),str(src)],cwd=root,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        elapsed=time.monotonic()-start
        log.write(f'COMMAND lake env lean -o {target.relative_to(root)} {src.relative_to(root)}\nSECONDS {elapsed:.3f}\n'+p.stdout+'\n'); log.flush()
        rows.append({'module':module,'seconds':round(elapsed,3),'exit_code':p.returncode})
        print(f'{module}: {elapsed:.3f}s exit {p.returncode}',flush=True)
        (report/'build-times.json').write_text(json.dumps(rows,indent=2)+'\n')
        if p.returncode: print(p.stdout,flush=True); sys.exit(p.returncode)
