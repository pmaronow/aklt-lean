import sys,json
sys.path.insert(0,'/home/ubuntu/aklt/reports/REL_FEAS')
from measure import *
env=ENV.copy();env['LEAN_PATH']=str(ST)+':'+LP
rr=[]
for sn in ['h3-raw-small','h3-prefix-empty']:
 orig=R/'measurements'/sn;d=json.loads((orig/'result.json').read_text())
 out=R/'exporter-native-validation'/sn
 rec=run([R/'fast-leanexport',d['module'],'--',*(orig/'roots.txt').read_text().split()],out,'native',env,300,22)
 rec.update(sample=sn,byte_identical=sha(out/'native.log')==sha(orig/'export.ndjson'),sha256=sha(out/'native.log'))
 rr.append(rec)
(R/'exporter-native-validation.json').write_text(json.dumps(rr,indent=2))
assert all(r['byte_identical'] for r in rr)
