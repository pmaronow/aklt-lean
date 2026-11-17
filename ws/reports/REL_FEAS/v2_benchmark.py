import sys,json
sys.path.insert(0,'/home/ubuntu/aklt/reports/REL_FEAS')
from measure import *
env=ENV.copy();env['LEAN_PATH']=str(ST)+':'+LP
rr=[]
for sn in ['h3-raw-small','h3-prefix-empty']:
 original=R/'measurements'/sn
 roots=(original/'roots.txt').read_text().split()
 mod=json.loads((original/'result.json').read_text())['module']
 out=R/'exporter-validation-v2'/sn
 rec=run([TC/'lean','--run',ST/'RELFEAS/FastMainV2.lean',mod,'--',*roots],out,'fast',env,300,22)
 rec.update(sample=sn,byte_identical=sha(out/'fast.log')==sha(original/'export.ndjson'),sha256=sha(out/'fast.log'))
 rr.append(rec)
(R/'exporter-v2-bench.json').write_text(json.dumps(rr,indent=2))
assert all(r['byte_identical'] for r in rr)
