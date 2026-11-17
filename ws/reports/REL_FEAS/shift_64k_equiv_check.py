import sys,json
sys.path.insert(0,'/home/ubuntu/aklt/reports/REL_FEAS')
from measure import *
out=R/'measurements/ShiftEquiv64K';e=out/'export.ndjson'
r=dict(module='RELFEAS.ShiftEquiv64K',roots=['Nat.div','Nat.mod']+['RELFEAS.ShiftEquiv64K.p'+str(k)+'_same' for k in range(64)],lean=json.loads((out/'lean.json').read_text()),export=json.loads((out/'export.json').read_text()),export_bytes=e.stat().st_size,export_sha256=sha(e))
cfg=dict(export_file_path=str(e),permitted_axioms=['propext','Classical.choice','Quot.sound'],unpermitted_axiom_hard_error=True,nat_extension=True,string_extension=True,print_success_message=True,num_threads=1)
(out/'nanoda-config.json').write_text(json.dumps(cfg))
for tag,cmd in [('conron',[TC/'con-ron','--verified','--jobs=1','--progress=1',e]),('nanoda',[TC/'nanoda_bin',out/'nanoda-config.json'])]:
 r[tag]=run(cmd,out,tag,ENV,300,7);t=(out/(tag+'.log')).read_text(errors='replace');r[tag]['accepts']=r[tag]['exit']==0 and ('declarations (--verified)' in t if tag=='conron' else 'no typechecker errors' in t)
r['harness_note']='Initial driver stopped after successful proof build and export because cfg was undefined following a stock-export timeout. This resumed checker-only run uses that same hashed export; no source/proof changed.'
(out/'result.json').write_text(json.dumps(r,indent=2))
