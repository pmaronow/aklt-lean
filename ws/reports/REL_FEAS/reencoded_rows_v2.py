import sys,json
sys.path.insert(0,'/home/ubuntu/aklt/reports/REL_FEAS')
from measure import *
env=ENV.copy();env['LEAN_PATH']=str(ST)+':'+LP
out=R/'measurements/h3-row-group-shift-v2';out.mkdir(parents=True,exist_ok=True)
roots=['Nat.div','Nat.mod']+(R/'measurements/h3-row-group/roots.txt').read_text().split()
r=dict(id='h3-row-group-shift-v2',module='RELFEAS.Rows',roots=roots,family='converted',
 conversion='only all nested large Nat literal expressions in definition values under CertData.H3 are encoded as balanced 8192-bit add/shift terms; types and proofs unchanged',
 prototype_only=True,exporter_sha256=sha(R/'reencode-export-v2'))
r['export']=run([R/'reencode-export-v2','RELFEAS.Rows','--',*roots],out,'export',env,2400,20)
if r['export']['exit']==0:
 e=out/'export.ndjson';(out/'export.log').rename(e);r['export_bytes']=e.stat().st_size;r['export_sha256']=sha(e)
 maxdigits=0;big=0
 with e.open() as f:
  for line in f:
   q=line.find('"natVal":"')
   if q>=0:
    n=line.rfind('"')-(q+10);maxdigits=max(maxdigits,n);big+=int(n>2500)
 r.update(max_nat_decimal_digits=maxdigits,nat_literal_records_over_2500_digits=big)
 cfg=dict(export_file_path=str(e),permitted_axioms=['propext','Classical.choice','Quot.sound'],unpermitted_axiom_hard_error=True,nat_extension=True,string_extension=True,print_success_message=True,num_threads=1)
 (out/'nanoda-config.json').write_text(json.dumps(cfg))
 for tag,cmd in [('conron',[TC/'con-ron','--verified','--jobs=1','--progress=1',e]),('nanoda',[TC/'nanoda_bin',out/'nanoda-config.json'])]:
  r[tag]=run(cmd,out,tag,env,900,15)
  t=(out/(tag+'.log')).read_text(errors='replace');r[tag]['accepts']=r[tag]['exit']==0 and ('declarations (--verified)' in t if tag=='conron' else 'no typechecker errors' in t)
(out/'result.json').write_text(json.dumps(r,indent=2))
