import sys,json
sys.path.insert(0,'/home/ubuntu/aklt/reports/REL_FEAS')
from measure import *
p=ST/'RELFEAS/MulOrderReformulated.lean';p.write_text('''import RELFEAS.MulOrderBigCoeff
namespace RELFEAS.MulOrderReformulated
open RELFEAS.MulOrderBigCoeff
theorem checked : 97632666219444*large = expected :=
  Eq.trans (Nat.mul_comm _ _) large_first
#print axioms checked
end RELFEAS.MulOrderReformulated
''')
env=ENV.copy();env['LEAN_PATH']=str(ST)+':'+LP;out=R/'measurements/MulOrderReformulated';r={}
r['lean']=run([TC/'lean','-o',p.with_suffix('.olean'),p],out,'lean',env,120,4)
if r['lean']['exit']==0:
 r['export']=run([R/'fast-leanexport','RELFEAS.MulOrderReformulated','--','Nat.div','Nat.mod','RELFEAS.MulOrderReformulated.checked'],out,'export',env,120,4)
 if r['export']['exit']==0:
  e=out/'export.ndjson';(out/'export.log').rename(e);r.update(export_bytes=e.stat().st_size,export_sha256=sha(e))
  cfg=dict(export_file_path=str(e),permitted_axioms=['propext','Classical.choice','Quot.sound'],unpermitted_axiom_hard_error=True,nat_extension=True,string_extension=True,print_success_message=True,num_threads=1);(out/'nanoda-config.json').write_text(json.dumps(cfg))
  for tag,cmd in [('conron',[TC/'con-ron','--verified','--jobs=1','--progress=1',e]),('nanoda',[TC/'nanoda_bin',out/'nanoda-config.json'])]:
   r[tag]=run(cmd,out,tag,env,60,4);t=(out/(tag+'.log')).read_text(errors='replace');r[tag]['accepts']=r[tag]['exit']==0 and ('declarations (--verified)' in t if tag=='conron' else 'no typechecker errors' in t)
(out/'result.json').write_text(json.dumps(r,indent=2))
