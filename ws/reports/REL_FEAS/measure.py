#!/usr/bin/env python3
"""Isolated, capped certificate-checker measurements. Never runs in a producer."""
import concurrent.futures,hashlib,json,os,pathlib,re,resource,shutil,signal,subprocess,sys,time
R=pathlib.Path('/home/ubuntu/aklt/reports/REL_FEAS'); WT=pathlib.Path('/home/ubuntu/aklt/wt/REL_FEAS')
TC=pathlib.Path.home()/'.elan/toolchains/leanprover--lean4---v4.35.0-rc2/bin'
ENV=os.environ.copy();ENV['PATH']=str(pathlib.Path.home()/'.elan/bin')+':'+ENV.get('PATH','');ENV['LEAN_NUM_THREADS']='1';ENV['PATH']=str(TC)+':'+ENV['PATH'];ENV['ELAN_TOOLCHAIN']='leanprover/lean4:v4.35.0-rc2'
LP=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=WT,env=ENV,text=True).strip()
ST=R/'scratch/lib';ST.mkdir(parents=True,exist_ok=True)

def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(8*1024*1024),b''): h.update(b)
 return h.hexdigest()

def prepare(samples):
 # Complete AKLT namespace overlay: copied producer H1 artifacts; all other paths read-only.
 ak=ST/'AKLT';ak.mkdir(exist_ok=True)
 base=WT/'.lake/build/lib/lean/AKLT'
 for p in base.iterdir():
  if p.name=='Cert':continue
  q=ak/p.name
  if not q.exists():q.symlink_to(p,target_is_directory=p.is_dir())
 (ak/'Cert').mkdir(exist_ok=True)
 for p in (base/'Cert').iterdir():
  if p.name=='H1':continue
  q=ak/'Cert'/p.name
  if not q.exists():q.symlink_to(p,target_is_directory=p.is_dir())
 lane=pathlib.Path('/home/ubuntu/aklt/wt/CERT_H1')
 dest=ak/'Cert/H1'
 if not dest.exists():shutil.copytree(lane/'AKLT/Cert/H1',dest,ignore=shutil.ignore_patterns('tools','Phase1','*.py','__pycache__'))
 copied={};seen=set()
 def copy(mod,family):
  if mod in seen:return
  seen.add(mod)
  if not mod.startswith('CertData.'):return
  src=pathlib.Path('/home/ubuntu/aklt/wt/CERT_'+family)/(mod.replace('.','/')+'.lean')
  obj=src.with_suffix('.olean');out=ST/(mod.replace('.','/')+'.olean')
  out.parent.mkdir(parents=True,exist_ok=True)
  if not obj.exists():raise RuntimeError('missing built artifact '+str(obj))
  if not out.exists():shutil.copy2(obj,out)
  copied[mod]={'from':str(obj),'bytes':out.stat().st_size,'sha256':sha(out)}
  if src.exists():
   # Sources of small support/check modules copied; huge packed literals stay in copied oleans.
   if src.stat().st_size<2_000_000:shutil.copy2(src,out.with_suffix('.lean'))
   for dep in re.findall(r'^import\s+(\S+)',src.read_text(),re.M):copy(dep,family)
  else:
   if family=='H3' and re.search(r'/B1/(Plane|Endpoint)/G[0-9]+[.]lean$',str(src)):
    copied[mod]['source_compacted']=True
    for dep in ['CertData.H3.Kernel.Common','CertData.H3.Kernel.Literal']:copy(dep,family)
   else:raise RuntimeError('source compacted; missing import inventory: '+str(src))
 for s in samples:copy(s['module'],s['family'])
 inv=R/'copied-artifacts.json'
 prior=json.loads(inv.read_text()) if inv.exists() else {}
 prior.update(copied);inv.write_text(json.dumps(prior,indent=2))
 print('prepared',len(copied),'artifacts',sum(x['bytes'] for x in copied.values()),flush=True)

def roots(src):
 ns=[];names=[]
 for line in src.read_text().splitlines():
  m=re.match(r'namespace\s+(\S+)',line)
  if m:ns.append(m[1])
  m=re.match(r'end(?:\s|$)',line)
  if m and ns:ns.pop()
  m=re.match(r'(?:noncomputable\s+)?(?:def|theorem|lemma|abbrev)\s+(\S+?)(?:\s|:|\()',line)
  if m:names.append('.'.join(ns+[m[1]]))
 return names

def run(cmd,out,tag,env,seconds=180,rss_gib=22):
 out.mkdir(parents=True,exist_ok=True); log=out/(tag+'.log');err=out/(tag+'.err');tm=out/(tag+'.time')
 def limit():
  resource.setrlimit(resource.RLIMIT_CORE,(0,0));resource.setrlimit(resource.RLIMIT_AS,(80*1024**3,80*1024**3))
 start=time.monotonic();peak=0;why=None
 with log.open('wb') as o,err.open('wb') as e:
  p=subprocess.Popen(['/usr/bin/time','-v','-o',str(tm),*map(str,cmd)],cwd=ST,env=env,stdout=o,stderr=e,start_new_session=True,preexec_fn=limit)
  while p.poll() is None:
   try:
    # Includes all descendants of the timed process, no unrelated producer processes.
    todo=[p.pid];rss=0
    while todo:
     pid=todo.pop();status=pathlib.Path(f'/proc/{pid}/status').read_text();m=re.search(r'^VmRSS:\s+(\d+)',status,re.M)
     if m:rss+=int(m[1])*1024
     try:todo += [int(x) for x in pathlib.Path(f'/proc/{pid}/task/{pid}/children').read_text().split()]
     except OSError:pass
    peak=max(peak,rss)
   except OSError:pass
   if peak>rss_gib*1024**3:why='RSS_CAP'
   if time.monotonic()-start>seconds:why='TIMEOUT'
   if shutil.disk_usage(R).free<50*1024**3:why='DISK_GUARD'
   if why:
    os.killpg(p.pid,signal.SIGTERM)
    try:p.wait(timeout=2)
    except subprocess.TimeoutExpired:os.killpg(p.pid,signal.SIGKILL)
    break
   time.sleep(.1)
  rc=p.wait()
 rec={'command':list(map(str,cmd)),'exit':rc,'wall_s':time.monotonic()-start,'sampled_peak_bytes':peak,'limit':why,'rss_cap_gib':rss_gib,'timeout_s':seconds}
 if tm.exists():
  txt=tm.read_text()
  for key,pat in [('user_s',r'User time \(seconds\): ([\d.]+)'),('system_s',r'System time \(seconds\): ([\d.]+)'),('rss_kib',r'Maximum resident set size \(kbytes\): (\d+)')]:
   m=re.search(pat,txt)
   if m:rec[key]=float(m[1])
 (out/(tag+'.json')).write_text(json.dumps(rec,indent=2))
 print(out.name,tag,'exit',rc,'seconds',round(rec['wall_s'],2),'GiB',round(peak/1024**3,3),why or '',flush=True)
 return rec

def measure(s):
 mod=s['module'];out=R/'measurements'/s['id'];out.mkdir(parents=True,exist_ok=True)
 src=ST/(mod.replace('.','/')+'.lean');names=roots(src)
 (out/'roots.txt').write_text('\n'.join(names)+'\n');env=ENV.copy();env['LEAN_PATH']=str(ST)+':'+LP
 results=dict(s,roots=names,source_sha256=sha(src))
 results['lean']=run([TC/'lean','-DautoImplicit=false','-DrelaxedAutoImplicit=false','-DElab.async=false','-o',src.with_suffix('.olean'),src],out,'lean',env,300)
 if results['lean']['exit']!=0:return results
 exp=run([TC/'lean','--run',ST/'RELFEAS/FastMain.lean',mod,'--',*names],out,'export',env,240)
 results['export']=exp
 if exp['exit']!=0:return results
 export=out/'export.ndjson';(out/'export.log').rename(export);results['export_bytes']=export.stat().st_size;results['export_sha256']=sha(export)
 cfg=dict(export_file_path=str(export),permitted_axioms=['propext','Classical.choice','Quot.sound'],unpermitted_axiom_hard_error=True,nat_extension=True,string_extension=True,print_success_message=True,num_threads=1)
 (out/'nanoda-config.json').write_text(json.dumps(cfg,indent=2))
 for tag,cmd in [('conron',[TC/'con-ron','--verified','--jobs=1','--progress=1',export]),('nanoda',[TC/'nanoda_bin',out/'nanoda-config.json'])]:
  r=run(cmd,out,tag,env,180,20);txt=(out/(tag+'.log')).read_text(errors='replace');r['accepts']=r['exit']==0 and ('accepted ' in txt and 'declarations (--verified)' in txt if tag=='conron' else 'no typechecker errors' in txt)
  results[tag]=r
 (out/'result.json').write_text(json.dumps(results,indent=2))
 # Keep export until diagnosis; finite disk guard managed below.
 return results

def samples():
 h3=[('row-small','CertData.H3.B1.Check.Rows.R0233'),('row-mid','CertData.H3.B1.Check.Rows.R0026'),('row-large','CertData.H3.B1.Check.Rows.R0011'),('prefix-empty','CertData.H3.B1.Check.Prefix.P0043'),('prefix-mid','CertData.H3.B1.Check.Prefix.P0116'),('prefix-large','CertData.H3.B1.Check.Prefix.P0106'),('raw-small','CertData.H3.Check.Raw.R0008'),('raw-large','CertData.H3.Check.Raw.R0063'),('reps','CertData.H3.Check.Representatives.R0000')]
 h1=[('gram-small','Gramrows0000'),('gram-heavy','Gramrows0005'),('gram-bundle','Gramrows0017'),('packed-small','Constructorrows0000'),('packed-heavy','Constructorrows0018'),('packed-wide','Constructorrows0029')]
 return [dict(id='h3-'+i,module=m,family='H3') for i,m in h3]+[dict(id='h1-'+i,module='CertData.H1.Generated.Pilot.'+m,family='H1') for i,m in h1]
if __name__=='__main__':
 ss=samples()
 if len(sys.argv)>1:ss=[s for s in ss if s['id'] in sys.argv[1:]]
 prepare(ss)
 with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
  for r in pool.map(measure,ss):
   with (R/'measurements.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
