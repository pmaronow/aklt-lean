import sys,json
sys.path.insert(0,'/home/ubuntu/aklt/reports/REL_FEAS')
from measure import *
mod='RELFEAS.PlaneShift64K';out=R/'measurements/PlaneShift64KNative'
env=ENV.copy();env['LEAN_PATH']=str(ST)+':'+LP
r=dict(module=mod,limb_bits=65536,roots=['Nat.div','Nat.mod',mod+'.checked'],lean=json.loads((R/'measurements/PlaneShift64K/lean.json').read_text()))
r['export']=run([R/'fast-leanexport',mod,'--',*r['roots']],out,'export',env,180,7)
if r['export']['exit']==0:
 e=out/'export.ndjson';(out/'export.log').rename(e);r.update(export_bytes=e.stat().st_size,export_sha256=sha(e))
 cfg=dict(export_file_path=str(e),permitted_axioms=['propext','Classical.choice','Quot.sound'],unpermitted_axiom_hard_error=True,nat_extension=True,string_extension=True,print_success_message=True,num_threads=1)
 (out/'nanoda-config.json').write_text(json.dumps(cfg))
 for tag,cmd in [('conron',[TC/'con-ron','--verified','--jobs=1','--progress=1',e]),('nanoda',[TC/'nanoda_bin',out/'nanoda-config.json'])]:
  r[tag]=run(cmd,out,tag,env,300,7);t=(out/(tag+'.log')).read_text(errors='replace');r[tag]['accepts']=r[tag]['exit']==0 and ('declarations (--verified)' in t if tag=='conron' else 'no typechecker errors' in t)
(out/'result.json').write_text(json.dumps(r,indent=2))
