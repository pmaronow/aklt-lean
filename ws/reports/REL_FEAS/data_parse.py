import sys,json
sys.path.insert(0,'/home/ubuntu/aklt/reports/REL_FEAS')
from measure import *
env=ENV.copy();env['LEAN_PATH']=str(ST)+':'+LP
mod='RELFEAS.PlaneLiteral';out=R/'measurements/PlaneDataOnly';roots=[mod+f'.p{k}' for k in range(64)]
r=dict(module=mod,roots=roots,planes=64)
r['export']=run([R/'fast-leanexport',mod,'--',*roots],out,'export',env,120,16)
e=out/'export.ndjson';(out/'export.log').rename(e);r['export_bytes']=e.stat().st_size
cfg=dict(export_file_path=str(e),permitted_axioms=['propext','Classical.choice','Quot.sound'],unpermitted_axiom_hard_error=True,nat_extension=True,string_extension=True,print_success_message=True,num_threads=1)
(out/'nanoda-config.json').write_text(json.dumps(cfg))
for tag,cmd in [('conron',[TC/'con-ron','--verified','--jobs=1','--progress=1',e]),('nanoda',[TC/'nanoda_bin',out/'nanoda-config.json'])]:
 r[tag]=run(cmd,out,tag,env,120,8)
 t=(out/(tag+'.log')).read_text(errors='replace');r[tag]['accepts']=r[tag]['exit']==0 and ('declarations (--verified)' in t if tag=='conron' else 'no typechecker errors' in t)
(out/'result.json').write_text(json.dumps(r,indent=2))
