import json,sys
sys.path.insert(0,'/home/ubuntu/aklt/reports/REL_FEAS')
from measure import *
import importlib.util
spec=importlib.util.spec_from_file_location('gate','/home/ubuntu/aklt/wt/REL_FEAS/release/release.py');gate=importlib.util.module_from_spec(spec);spec.loader.exec_module(gate)
env=ENV.copy();env['LEAN_PATH']=str(ST)+':'+LP
out=R/'measurements/ComparatorShift64';out.mkdir(parents=True,exist_ok=True)
mod='RELFEAS.PlaneShift'
r={'module':mod,'scope':'self-comparison; default Lean only, to isolate Comparator costs'}
r['export']=run([R/'fast-leanexport',mod,'--',*gate.PRIMS,mod+'.checked'],out,'export',env,120,12)
e=out/'export.ndjson';(out/'export.log').rename(e)
cfg=dict(challenge_module=mod,solution_module=mod,theorem_names=[mod+'.checked'],definition_names=[],permitted_axioms=['propext','Classical.choice','Quot.sound'],external_kernels={})
(out/'comparator.json').write_text(json.dumps(cfg))
r['comparator']=run([TC/'lake','comparator','--config',out/'comparator.json','--challenge-from-export',e,'--solution-from-export',e],out,'comparator',env,600,8)
r['comparator']['accepts']=r['comparator']['exit']==0 and 'Your solution is okay!' in (out/'comparator.log').read_text()
(out/'result.json').write_text(json.dumps(r,indent=2))
