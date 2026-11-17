import sys,json,importlib.util
sys.path.insert(0,'/home/ubuntu/aklt/reports/REL_FEAS')
from measure import *
spec=importlib.util.spec_from_file_location('gate','/home/ubuntu/aklt/wt/REL_FEAS/release/release.py')
gate=importlib.util.module_from_spec(spec);spec.loader.exec_module(gate)
env=ENV.copy();env['LEAN_PATH']=str(ST)+':'+LP
rr=[]
cases=[]
for k in [128,4096,16384,65536]:
 cases.append(('MulPow'+str(k),f'((2:Nat)^{k}+1) * (2^{k}+1) = 2^{2*k} + 2^{k+1} + 1'))
cases.append(('ShiftPow65536','Nat.shiftLeft ((2:Nat)^65536+1) 65536 = 2^131072+2^65536'))
for name,goal in cases:
 mod='RELFEAS.'+name;p=ST/'RELFEAS'/f'{name}.lean'
 p.write_text('import Lean.Elab.Tactic.Decide\nimport Init.Data.Nat.Bitwise.Lemmas\nset_option maxHeartbeats 1000000000\nnamespace '+mod+'\ntheorem checked : '+goal+' := by decide +kernel\n#print axioms checked\nend '+mod+'\n')
 out=R/'measurements'/name;r=dict(module=mod,goal=goal)
 r['lean']=run([TC/'lean','-o',p.with_suffix('.olean'),p],out,'lean',env,60,1.5)
 if r['lean']['exit']:rr.append(r);continue
 roots=(gate.PRIMS if name.startswith('Shift') else [])+[mod+'.checked']
 r['export']=run([TC/'leanexport',mod,'--',*roots],out,'export',env,60,1.5)
 e=out/'export.ndjson';(out/'export.log').rename(e)
 r['conron']=run([TC/'con-ron','--verified','--jobs=1','--progress=1',e],out,'conron',env,45,1.5)
 t=(out/'conron.log').read_text();r['conron']['accepts']=r['conron']['exit']==0 and 'declarations (--verified)' in t
 cfg=dict(export_file_path=str(e),permitted_axioms=['propext','Classical.choice','Quot.sound'],unpermitted_axiom_hard_error=True,nat_extension=True,string_extension=True,print_success_message=True,num_threads=1)
 (out/'nanoda-config.json').write_text(json.dumps(cfg))
 r['nanoda']=run([TC/'nanoda_bin',out/'nanoda-config.json'],out,'nanoda',env,45,1.5)
 t=(out/'nanoda.log').read_text();r['nanoda']['accepts']=r['nanoda']['exit']==0 and 'no typechecker errors' in t
 (out/'result.json').write_text(json.dumps(r,indent=2));rr.append(r)
(R/'nested-op-results.json').write_text(json.dumps(rr,indent=2))
