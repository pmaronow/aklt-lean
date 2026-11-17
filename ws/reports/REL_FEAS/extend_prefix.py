import sys,json
sys.path.insert(0,'/home/ubuntu/aklt/reports/REL_FEAS')
from measure import *
out=R/'measurements/h3-prefix-large-extended';e=R/'measurements/h3-prefix-large/export.ndjson'
env=ENV.copy();r=run([TC/'con-ron','--verified','--jobs=1','--progress=1',e],out,'conron',env,600,20)
r['accepts']=r['exit']==0 and 'declarations (--verified)' in (out/'conron.log').read_text()
(out/'result.json').write_text(json.dumps(r,indent=2))
