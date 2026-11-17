import sys,json,re
sys.path.insert(0,'/home/ubuntu/aklt/reports/REL_FEAS')
from measure import *
sys.set_int_max_str_digits(0)
oldsrc=(ST/'RELFEAS/PlaneLiteral.lean').read_text()
values={int(k):int(v,16) for k,v in re.findall(r'^def p([0-9]+) : Nat := h3_hex% "([0-9a-f]+)"',oldsrc,re.M)}
assert sorted(values)==list(range(64))
def literal(n):return 'h3_hex% "'+format(n,'x')+'"'
def limbs(n):
 width=8192;ls=[]
 while n:ls.append(n & ((1<<width)-1));n >>= width
 def go(xs):
  if not xs:return '0'
  if len(xs)==1:return literal(xs[0])
  mid=len(xs)//2
  return '('+go(xs[:mid])+' + 2^'+str(width*mid)+' * '+go(xs[mid:])+')'
 return go(ls)
env=ENV.copy();env['LEAN_PATH']=str(ST)+':'+LP
results=[json.loads((R/'measurements/PlaneLiteral/result.json').read_text())]
for style,encode in [('PlaneLimbs',limbs)]:
 mod='RELFEAS.'+style;src=ST/'RELFEAS'/f'{style}.lean'
 src.write_text('import CertData.H3.Kernel.Common\nimport CertData.H3.Kernel.Literal\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 1000000000\nnamespace '+mod+'\n'+
  '\n'.join('def p'+str(k)+' : Nat := '+encode(v) for k,v in sorted(values.items()))+
  '\ndef planes : List Nat := ['+','.join('p'+str(k) for k in range(64))+']\n'+
  'theorem checked : planes.all (fun p => decide ((p >>> 795200) % 2^80 = 0)) = true := by decide +kernel\n#print axioms checked\nend '+mod+'\n')
 out=R/'measurements'/style;r=dict(id=style,module=mod,planes=64,limb_bits=8192 if style=='PlaneLimbs' else None,roots=[mod+'.checked'])
 r['lean']=run([TC/'lean','-DElab.async=false','-o',src.with_suffix('.olean'),src],out,'lean',env,300,20)
 if r['lean']['exit']:
  results.append(r);continue
 r['stock_export']=run([TC/'leanexport',mod,'--',mod+'.checked'],out,'stock',env,120,20)
 if r['stock_export']['exit']==0:
  e=out/'export.ndjson';(out/'stock.log').rename(e)
 else:
  r['native_export']=run([R/'fast-leanexport',mod,'--',mod+'.checked'],out,'export',env,300,20)
  e=out/'export.ndjson';(out/'export.log').rename(e)
 r['export_bytes']=e.stat().st_size;r['export_sha256']=sha(e)
 cfg=dict(export_file_path=str(e),permitted_axioms=['propext','Classical.choice','Quot.sound'],
  unpermitted_axiom_hard_error=True,nat_extension=True,string_extension=True,print_success_message=True,num_threads=1)
 (out/'nanoda-config.json').write_text(json.dumps(cfg))
 for tag,cmd in [('conron',[TC/'con-ron','--verified','--jobs=1','--progress=1',e]),
                 ('nanoda',[TC/'nanoda_bin',out/'nanoda-config.json'])]:
  r[tag]=run(cmd,out,tag,env,300,20);t=(out/(tag+'.log')).read_text(errors='replace')
  r[tag]['accepts']=r[tag]['exit']==0 and ('declarations (--verified)' in t if tag=='conron' else 'no typechecker errors' in t)
 (out/'result.json').write_text(json.dumps(r,indent=2));results.append(r)
(R/'limb-results.json').write_text(json.dumps(results,indent=2))
# Bind every converted value back to the actual supplied data, in Lean and both checkers.
mod='RELFEAS.PlaneEquiv';src=ST/'RELFEAS/PlaneEquiv.lean'
src.write_text('import RELFEAS.PlaneLimbs\nimport CertData.H3.B1.Plane.G0000\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 1000000000\nnamespace '+mod+'\n'+
 '\n'.join(f'theorem p{k}_same : RELFEAS.PlaneLimbs.p{k} = CertData.H3.B1.Plane.G0000.p{k} := by decide +kernel\n#print axioms p{k}_same' for k in range(64))+'\nend '+mod+'\n')
out=R/'measurements/PlaneEquiv'
r=dict(module=mod,roots=[mod+f'.p{k}_same' for k in range(64)])
r['lean']=run([TC/'lean','-DElab.async=false','-o',src.with_suffix('.olean'),src],out,'lean',env,300,20)
if not r['lean']['exit']:
 r['export']=run([R/'fast-leanexport',mod,'--',*r['roots']],out,'export',env,300,20)
 e=out/'export.ndjson';(out/'export.log').rename(e)
 cfg=dict(export_file_path=str(e),permitted_axioms=['propext','Classical.choice','Quot.sound'],unpermitted_axiom_hard_error=True,nat_extension=True,string_extension=True,print_success_message=True,num_threads=1)
 (out/'nanoda-config.json').write_text(json.dumps(cfg))
 for tag,cmd in [('conron',[TC/'con-ron','--verified','--jobs=1','--progress=1',e]),('nanoda',[TC/'nanoda_bin',out/'nanoda-config.json'])]:
  r[tag]=run(cmd,out,tag,env,300,20)
  t=(out/(tag+'.log')).read_text(errors='replace');r[tag]['accepts']=r[tag]['exit']==0 and ('declarations (--verified)' in t if tag=='conron' else 'no typechecker errors' in t)
(out/'result.json').write_text(json.dumps(r,indent=2))
