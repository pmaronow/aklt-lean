import concurrent.futures,json,sys
sys.path.insert(0,'/home/ubuntu/aklt/reports/REL_FEAS')
from measure import *
s=dict(id='h1-packed-owner',module='CertData.H1.Generated.Pilot.Constructorrows0029',family='H1')
prepare([s]);mod=s['module'];src=ST/(mod.replace('.','/')+'.lean');out=R/'measurements'/s['id'];out.mkdir(parents=True,exist_ok=True)
env=ENV.copy();env['LEAN_PATH']=str(ST)+':'+LP
names=roots(src);(out/'roots.txt').write_text('\n'.join(names)+'\n')
r=dict(s,roots=names,source_sha256=sha(src),checker_workers=2)
r['lean']=run([TC/'lean','-DautoImplicit=false','-DrelaxedAutoImplicit=false','-DElab.async=false','-o',src.with_suffix('.olean'),src],out,'lean',env,1200,15)
if r['lean']['exit']==0:
 r['export']=run([R/'fast-leanexport',mod,'--',*names],out,'export',env,300,15)
 if r['export']['exit']==0:
  e=out/'export.ndjson';(out/'export.log').rename(e);r.update(export_bytes=e.stat().st_size,export_sha256=sha(e))
  cfg=dict(export_file_path=str(e),permitted_axioms=['propext','Classical.choice','Quot.sound'],unpermitted_axiom_hard_error=True,nat_extension=True,string_extension=True,print_success_message=True,num_threads=2)
  (out/'nanoda-config.json').write_text(json.dumps(cfg))
  def one(tag):
   cmd=[TC/'con-ron','--verified','--jobs=2','--progress=1',e] if tag=='conron' else [TC/'nanoda_bin',out/'nanoda-config.json']
   q=run(cmd,out,tag,env,1800,15);txt=(out/(tag+'.log')).read_text(errors='replace')
   q['accepts']=q['exit']==0 and ('declarations (--verified)' in txt if tag=='conron' else 'no typechecker errors' in txt)
   return tag,q
  with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:r.update(dict(pool.map(one,['conron','nanoda'])))
(out/'result.json').write_text(json.dumps(r,indent=2))
