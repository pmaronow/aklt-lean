import concurrent.futures,json,pathlib,sys
sys.path.insert(0,'/home/ubuntu/aklt/reports/REL_FEAS')
from measure import *
# Small, exact kernel terms isolate operation support, with the same syntactic proof form as production.
PROBES={
 'NatMul': 'theorem checked : (340282366920938463463374607431768211457 : Nat) * 340282366920938463463374607431768211457 = 115792089237316195423570985008687907853950549399482440966384333222776666062849 := by decide +kernel',
 'IntMul': 'theorem checked : (-340282366920938463463374607431768211457 : Int) * 340282366920938463463374607431768211457 = -115792089237316195423570985008687907853950549399482440966384333222776666062849 := by decide +kernel',
 'ShiftRight': 'theorem checked : (3 : Nat) >>> 1000000 = 0 := by decide +kernel',
 'ShiftRightDiv': 'theorem checked : (3 : Nat) >>> 1000000 = 0 := by\n  rw [Nat.shiftRight_eq_div_pow]\n  decide +kernel',
 'ShiftLeft': 'theorem checked : (1 : Nat) <<< 100000 = 2^100000 := by decide +kernel',
 'ShiftLeftMul': 'theorem checked : (1 : Nat) <<< 100000 = 2^100000 := by\n  rw [Nat.shiftLeft_eq]\n  exact Nat.one_mul _',
 'And': 'theorem checked : Nat.land (2^4096-1) (2^2048-1) = 2^2048-1 := by decide +kernel',
 'Pow': 'theorem checked : (2:Nat)^100000 % 17 = 1 := by decide +kernel',
 'Rec': 'def count : Nat → Nat\n | 0 => 0\n | n+1 => count n+1\ntheorem checked : count 10000 = 10000 := by decide +kernel',
 'List': 'def xs : List Nat := ['+','.join(str(i) for i in range(1000))+']\ntheorem checked : xs.sum = 499500 := by decide +kernel',
}
def probe(k):
 mod='RELFEAS.'+k;src=ST/(mod.replace('.','/')+'.lean');src.parent.mkdir(exist_ok=True)
 src.write_text('import Lean.Elab.Tactic.Decide\nimport Init.Data.Nat.Bitwise.Lemmas\nset_option maxRecDepth 20000\nset_option maxHeartbeats 10000000\nnamespace RELFEAS.'+k+'\n'+PROBES[k]+'\n#print axioms checked\nend RELFEAS.'+k+'\n')
 s=dict(id='probe-'+k,module=mod,family='probe');out=R/'measurements'/s['id'];out.mkdir(parents=True,exist_ok=True)
 env=ENV.copy();env['LEAN_PATH']=str(ST)+':'+LP
 r=dict(s,roots=[mod+'.checked'])
 r['lean']=run([TC/'lean','-DElab.async=false','-o',src.with_suffix('.olean'),src],out,'lean',env,90,8)
 if r['lean']['exit']:return r
 r['export']=run([TC/'leanexport',mod,'--',mod+'.checked'],out,'export',env,90,8)
 if r['export']['exit']:return r
 e=out/'export.ndjson';(out/'export.log').rename(e);r['export_bytes']=e.stat().st_size
 cfg=dict(export_file_path=str(e),permitted_axioms=['propext','Classical.choice','Quot.sound'],unpermitted_axiom_hard_error=True,nat_extension=True,string_extension=True,print_success_message=True,num_threads=1)
 (out/'nanoda-config.json').write_text(json.dumps(cfg))
 for tag,cmd in [('conron',[TC/'con-ron','--verified','--jobs=1','--progress=1',e]),('nanoda',[TC/'nanoda_bin',out/'nanoda-config.json'])]:
  r[tag]=run(cmd,out,tag,env,60,6);t=(out/(tag+'.log')).read_text(errors='replace');r[tag]['accepts']=r[tag]['exit']==0 and ('declarations (--verified)' in t if tag=='conron' else 'no typechecker errors' in t)
 (out/'result.json').write_text(json.dumps(r,indent=2));return r
if __name__=='__main__':
 keys=sys.argv[1:] or list(PROBES)
 with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
  for r in pool.map(probe,keys):
   with (R/'probes.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
