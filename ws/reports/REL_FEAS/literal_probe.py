import sys,json
sys.path.insert(0,'/home/ubuntu/aklt/reports/REL_FEAS')
from measure import *
bits=12582912;mod='RELFEAS.Literal';src=ST/'RELFEAS/Literal.lean'
src.write_text('import CertData.H3.Kernel.Literal\nnamespace '+mod+'\ndef huge : Nat := h3_hex% "'+'f'*(bits//4)+'"\ntheorem checked : huge = huge := rfl\n#print axioms checked\nend '+mod+'\n')
env=ENV.copy();env['LEAN_PATH']=str(ST)+':'+LP
out=R/'measurements/probe-Literal';r=dict(module=mod,bits=bits,source_sha256=sha(src),roots=[mod+'.checked'])
r['lean']=run([TC/'lean','-o',src.with_suffix('.olean'),src],out,'lean',env,120,10)
r['stock_export']=run([TC/'leanexport',mod,'--',mod+'.checked'],out,'stock',env,120,10)
r['native_export']=run([R/'fast-leanexport',mod,'--',mod+'.checked'],out,'export',env,120,10)
e=out/'export.ndjson';(out/'export.log').rename(e);r['export_bytes']=e.stat().st_size
cfg=dict(export_file_path=str(e),permitted_axioms=['propext','Classical.choice','Quot.sound'],
 unpermitted_axiom_hard_error=True,nat_extension=True,string_extension=True,print_success_message=True,num_threads=1)
(out/'nanoda-config.json').write_text(json.dumps(cfg))
for tag,cmd in [('conron',[TC/'con-ron','--verified','--jobs=1','--progress=1',e]),
                ('nanoda',[TC/'nanoda_bin',out/'nanoda-config.json'])]:
 r[tag]=run(cmd,out,tag,env,120,6)
 t=(out/(tag+'.log')).read_text(errors='replace');r[tag]['accepts']=r[tag]['exit']==0 and ('declarations (--verified)' in t if tag=='conron' else 'no typechecker errors' in t)
(out/'result.json').write_text(json.dumps(r,indent=2))
