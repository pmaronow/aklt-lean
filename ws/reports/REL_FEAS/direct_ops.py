import json,sys
sys.path.insert(0,'/home/ubuntu/aklt/reports/REL_FEAS')
from measure import *
env=ENV.copy();env['LEAN_PATH']=str(ST)+':'+LP
cases=[
 ('Direct128','Nat.add 7 (Nat.mul (Nat.pow 2 128) 23) = 7 + 2^128*23'),
 ('Direct65536','Nat.add 7 (Nat.mul (Nat.pow 2 65536) 23) = 7 + 2^65536*23'),
 ('Direct786432','Nat.add 7 (Nat.mul (Nat.pow 2 786432) 23) = 7 + 2^786432*23'),
 ('MulPow786432','((2:Nat)^786432+1) * (2^786432+1) = 2^1572864 + 2^786433 + 1'),
 ('Shift786432','Nat.shiftLeft ((2:Nat)^786432+1) 786432 = 2^1572864+2^786432')]
rr=[]
for name,goal in cases:
 mod='RELFEAS.'+name;p=ST/'RELFEAS'/f'{name}.lean'
 p.write_text('import Lean.Elab.Tactic.Decide\nimport Init.Data.Nat.Bitwise.Lemmas\nset_option maxHeartbeats 1000000000\nnamespace '+mod+'\ntheorem checked : '+goal+' := by decide +kernel\n#print axioms checked\nend '+mod+'\n')
 out=R/'measurements'/name;r=dict(module=mod,goal=goal)
 r['lean']=run([TC/'lean','-o',p.with_suffix('.olean'),p],out,'lean',env,120,3)
 if r['lean']['exit']:rr.append(r);continue
 roots=[mod+'.checked']
 if name.startswith('Shift'):roots=['Nat.div','Nat.mod']+roots
 r['export']=run([TC/'leanexport',mod,'--',*roots],out,'export',env,120,3)
 e=out/'export.ndjson';(out/'export.log').rename(e)
 r['conron']=run([TC/'con-ron','--verified','--jobs=1','--progress=1',e],out,'conron',env,45,3)
 r['conron']['accepts']=r['conron']['exit']==0 and 'declarations (--verified)' in (out/'conron.log').read_text()
 cfg=dict(export_file_path=str(e),permitted_axioms=['propext','Classical.choice','Quot.sound'],unpermitted_axiom_hard_error=True,nat_extension=True,string_extension=True,print_success_message=True,num_threads=1)
 (out/'nanoda-config.json').write_text(json.dumps(cfg))
 r['nanoda']=run([TC/'nanoda_bin',out/'nanoda-config.json'],out,'nanoda',env,45,3)
 r['nanoda']['accepts']=r['nanoda']['exit']==0 and 'no typechecker errors' in (out/'nanoda.log').read_text()
 (out/'result.json').write_text(json.dumps(r,indent=2));rr.append(r)
(R/'direct-op-results.json').write_text(json.dumps(rr,indent=2))
