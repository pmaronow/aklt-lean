import sys,json
sys.path.insert(0,'/home/ubuntu/aklt/reports/REL_FEAS')
import measure as m
st=m.ST;env=m.ENV.copy();env['LEAN_PATH']=str(st)+':'+m.LP
macro='''import CertData.H3.Kernel.Literal
namespace RELFEAS.ShiftHex
open Lean Elab Term
def encode : Nat → Nat → Expr
  | 0, n => mkNatLit n
  | fuel+1, n =>
    let bits := n.log2+1
    if bits ≤ 8192 then mkNatLit n else
      let cut := 8192 * (max 1 (((bits+8191)/8192)/2))
      let low := Nat.land n (2^cut-1)
      let high := n >>> cut
      mkApp2 (mkConst @Q@Nat.add) (encode fuel low)
        (mkApp2 (mkConst @Q@Nat.shiftLeft) (encode fuel high) (mkNatLit cut))
syntax (name := limbHex) "limb_hex% " str : term
@[term_elab limbHex] def elabShiftHex : TermElab := fun stx _ => do
  let some s := stx[1].isStrLit? | throwError "expected hex string"
  return encode 64 (AKLT.Cert.H3.decodeHexBalanced s)
end RELFEAS.ShiftHex
'''.replace('@Q@',chr(96)*2)
p=st/'RELFEAS/ShiftHex.lean';p.write_text(macro)
out=m.R/'measurements/PlaneShift'
r=dict(id='PlaneShift',module='RELFEAS.PlaneShift',limb_bits=8192,planes=64)
r['macro_build']=m.run([m.TC/'lean','-o',p.with_suffix('.olean'),p],out,'macro-build',env,120,6)
src=st/'RELFEAS/PlaneShift.lean'
text=(st/'RELFEAS/PlaneLiteral.lean').read_text().replace('import CertData.H3.Kernel.Common\n','').replace('import CertData.H3.Kernel.Literal','import RELFEAS.ShiftHex').replace('RELFEAS.PlaneLiteral','RELFEAS.PlaneShift').replace('h3_hex%','limb_hex%')
src.write_text(text)
r['lean']=m.run([m.TC/'lean','-DElab.async=false','-o',src.with_suffix('.olean'),src],out,'lean',env,600,6)
if r['lean']['exit']==0:
 r['export']=m.run([m.TC/'leanexport',r['module'],'--','Nat.div','Nat.mod',r['module']+'.checked'],out,'export',env,120,7)
 if r['export']['exit']==0:
  e=out/'export.ndjson';(out/'export.log').rename(e);r['export_bytes']=e.stat().st_size;r['export_sha256']=m.sha(e)
  cfg=dict(export_file_path=str(e),permitted_axioms=['propext','Classical.choice','Quot.sound'],unpermitted_axiom_hard_error=True,nat_extension=True,string_extension=True,print_success_message=True,num_threads=1)
  (out/'nanoda-config.json').write_text(json.dumps(cfg))
  for tag,cmd in [('conron',[m.TC/'con-ron','--verified','--jobs=1','--progress=1',e]),('nanoda',[m.TC/'nanoda_bin',out/'nanoda-config.json'])]:
   r[tag]=m.run(cmd,out,tag,env,300,6)
   t=(out/(tag+'.log')).read_text(errors='replace');r[tag]['accepts']=r[tag]['exit']==0 and ('declarations (--verified)' in t if tag=='conron' else 'no typechecker errors' in t)
(out/'result.json').write_text(json.dumps(r,indent=2))
# Equivalence with all 64 actual certificate literals; this is validation, not a production import.
if r['lean']['exit']==0:
 mod='RELFEAS.ShiftEquiv';p=st/'RELFEAS/ShiftEquiv.lean'
 p.write_text('import RELFEAS.PlaneShift\nimport CertData.H3.B1.Plane.G0000\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 1000000000\nnamespace '+mod+'\n'+
  '\n'.join(f'theorem p{k}_same : RELFEAS.PlaneShift.p{k} = CertData.H3.B1.Plane.G0000.p{k} := by decide +kernel\n#print axioms p{k}_same' for k in range(64))+'\nend '+mod+'\n')
 out=m.R/'measurements/ShiftEquiv';rr={'module':mod,'roots':[mod+f'.p{k}_same' for k in range(64)]}
 rr['lean']=m.run([m.TC/'lean','-DElab.async=false','-o',p.with_suffix('.olean'),p],out,'lean',env,300,7)
 if rr['lean']['exit']==0:
  rr['export']=m.run([m.R/'fast-leanexport',mod,'--',*rr['roots']],out,'export',env,120,7)
  if rr['export']['exit']==0:
   e=out/'export.ndjson';(out/'export.log').rename(e)
   cfg['export_file_path']=str(e);(out/'nanoda-config.json').write_text(json.dumps(cfg))
   for tag,cmd in [('conron',[m.TC/'con-ron','--verified','--jobs=1','--progress=1',e]),('nanoda',[m.TC/'nanoda_bin',out/'nanoda-config.json'])]:
    rr[tag]=m.run(cmd,out,tag,env,300,6)
    t=(out/(tag+'.log')).read_text(errors='replace');rr[tag]['accepts']=rr[tag]['exit']==0 and ('declarations (--verified)' in t if tag=='conron' else 'no typechecker errors' in t)
 (out/'result.json').write_text(json.dumps(rr,indent=2))
