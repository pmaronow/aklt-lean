from pathlib import Path
import os,re,subprocess,concurrent.futures,time,json,sys
ROOT=Path('/home/ubuntu/aklt/wt/VENDOR_1'); OUT=Path('/home/ubuntu/aklt/reports/VENDOR_1')
LOG=OUT/'build'; LOG.mkdir(exist_ok=True)
mods={str(p.relative_to(ROOT)).removesuffix('.lean').replace('/','.'):p for p in (ROOT/'AKLT/Vendor').rglob('*.lean')}
imports={m:re.findall(r'^(?:public )?import ([\w.]+)',p.read_text(),re.M) for m,p in mods.items()}
env={**os.environ,'PATH':'/home/ubuntu/.elan/bin:'+os.environ['PATH'],'LEAN_NUM_THREADS':'1'}
pending=set(mods);running={};results={};start=time.monotonic()
prior=OUT/'build-results.json'
# Reuse successful builds for unchanged source only.
import hashlib
if prior.exists() and '--fresh' not in sys.argv:
 for m,v in json.loads(prior.read_text()).get('results',{}).items():
  obj=ROOT/'.lake/build/lib/lean'/(m.replace('.','/')+'.olean')
  if m in mods and v['status']=='ok' and v.get('sha256')==hashlib.sha256(mods[m].read_bytes()).hexdigest() and obj.exists():results[m]=v;pending.discard(m)
# A changed dependency invalidates a cached dependent even when its source is unchanged.
while True:
 invalid=[m for m in results if any(d in mods and d not in results for d in imports[m])]
 if not invalid:break
 for m in invalid:del results[m];pending.add(m)
def run(m):
 t=time.monotonic();obj=ROOT/'.lake/build/lib/lean'/(m.replace('.','/')+'.olean');obj.parent.mkdir(parents=True,exist_ok=True)
 cmd=['lake','env','lean','-DautoImplicit=false','-DrelaxedAutoImplicit=false','-o',str(obj),str(mods[m].relative_to(ROOT))]
 p=subprocess.run(cmd,cwd=ROOT,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=300)
 (LOG/(m+'.log')).write_text(p.stdout)
 return dict(status='ok' if p.returncode==0 else 'failed',returncode=p.returncode,seconds=time.monotonic()-t,command=cmd,sha256=hashlib.sha256(mods[m].read_bytes()).hexdigest())
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
 while pending or running:
  for m in sorted(pending):
   deps=[x for x in imports[m] if x in mods]
   bad=[d for d in deps if d in results and results[d]['status']!='ok']
   if bad:results[m]=dict(status='blocked',dependencies=bad);pending.remove(m);continue
   if len(running)<4 and all(d in results for d in deps):running[pool.submit(run,m)]=m;pending.remove(m)
  if running:
   done,_=concurrent.futures.wait(running,timeout=3,return_when=concurrent.futures.FIRST_COMPLETED)
   for f in done:
    m=running.pop(f);results[m]=f.result();print(m,results[m]['status'],round(results[m]['seconds'],2),flush=True)
  elif pending:continue
  summary=dict(seconds=time.monotonic()-start,max_lean_processes=4,results=results)
  prior.write_text(json.dumps(summary,indent=2)+'\n')
print({s:sum(v['status']==s for v in results.values()) for s in ['ok','failed','blocked']},flush=True)
