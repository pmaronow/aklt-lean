from pathlib import Path
import sys,os,subprocess,time,json
root=Path('/home/ubuntu/aklt/wt/BP_H1M');report=Path('/home/ubuntu/aklt/reports/BP_H1M')
env=os.environ.copy();env['PATH']=str(Path.home()/'.elan/bin')+':'+env['PATH']
seen=set();order=[]
def visit(m):
 if m in seen:return
 seen.add(m);p=root/(m.replace('.','/')+'.lean')
 if not p.exists():return
 for line in p.read_text().splitlines():
  if line.startswith('import '):
   for d in line[7:].split():
    if d.startswith('AKLT.'):visit(d)
 order.append(m)
for m in sys.argv[1:]:visit(m)
rows=[]
with (report/'adaptation-build.log').open('a') as log:
 for m in order:
  source=root/(m.replace('.','/')+'.lean');target=root/'.lake/build/lib/lean'/(m.replace('.','/')+'.olean')
  target.parent.mkdir(parents=True,exist_ok=True)
  if '--' not in m and target.exists() and target.stat().st_mtime>source.stat().st_mtime and os.environ.get('H1_ADAPT_INCREMENTAL')=='1':continue
  start=time.monotonic();cmd=['lake','env','lean','-DautoImplicit=false','-DrelaxedAutoImplicit=false','-o',str(target),str(source)]
  p=subprocess.run(cmd,cwd=root,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True);elapsed=round(time.monotonic()-start,3)
  row={'module':m,'seconds':elapsed,'exit_code':p.returncode,'command':cmd};rows.append(row)
  print(m,elapsed,'seconds exit',p.returncode,flush=True)
  log.write(json.dumps(row)+'\n'+p.stdout+'\n');log.flush()
  old=json.loads((report/'adaptation-build-times.json').read_text()) if (report/'adaptation-build-times.json').exists() else []
  old.append(row);(report/'adaptation-build-times.json').write_text(json.dumps(old,indent=2)+'\n')
  if p.returncode:print(p.stdout,flush=True);raise SystemExit(p.returncode)
