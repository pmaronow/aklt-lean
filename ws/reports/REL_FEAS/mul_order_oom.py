import sys,json,concurrent.futures
sys.path.insert(0,'/home/ubuntu/aklt/reports/REL_FEAS')
from measure import *
env=ENV.copy();env['LEAN_PATH']=str(ST)+':'+LP
p=ST/'RELFEAS/MulOrderOOM.lean'
p.write_text('''import Init
namespace RELFEAS.MulOrderOOM
def large : Nat := 2^2097152-1
def expected : Nat := (Nat.shiftLeft 97632666219444 2097152)-97632666219444
theorem small_first : 97632666219444*large = expected := by decide +kernel
#print axioms small_first
theorem large_first : large*97632666219444 = expected := by decide +kernel
#print axioms large_first
end RELFEAS.MulOrderOOM
''')
out=R/'measurements/MulOrderOOM';r={}
r['lean']=run([TC/'lean','-DElab.async=false','-o',p.with_suffix('.olean'),p],out,'lean',env,120,4)
results={}
if r['lean']['exit']==0:
 for name in ['small_first','large_first']:
  q=dict(roots=['Nat.div','Nat.mod','RELFEAS.MulOrderOOM.'+name],lean=r['lean'])
  d=R/'measurements'/('MulOrderOOM-'+name)
  q['export']=run([R/'fast-leanexport','RELFEAS.MulOrderOOM','--',*q['roots']],d,'export',env,120,4)
  if q['export']['exit']==0:
   e=d/'export.ndjson';(d/'export.log').rename(e);q.update(export_bytes=e.stat().st_size,export_sha256=sha(e))
   cfg=dict(export_file_path=str(e),permitted_axioms=['propext','Classical.choice','Quot.sound'],unpermitted_axiom_hard_error=True,nat_extension=True,string_extension=True,print_success_message=True,num_threads=1)
   (d/'nanoda-config.json').write_text(json.dumps(cfg))
   def one(tag):
    cmd=[TC/'con-ron','--verified','--jobs=1','--progress=1',e] if tag=='conron' else [TC/'nanoda_bin',d/'nanoda-config.json']
    z=run(cmd,d,tag,env,60,4);t=(d/(tag+'.log')).read_text(errors='replace');z['accepts']=z['exit']==0 and ('declarations (--verified)' in t if tag=='conron' else 'no typechecker errors' in t)
    return tag,z
   with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:q.update(dict(pool.map(one,['conron','nanoda'])))
  (d/'result.json').write_text(json.dumps(q,indent=2));results[name]=q
r['variants']=results
(out/'result.json').write_text(json.dumps(r,indent=2))
