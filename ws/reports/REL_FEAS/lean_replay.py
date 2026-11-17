import sys,json
sys.path.insert(0,'/home/ubuntu/aklt/reports/REL_FEAS')
from measure import *
rr=[]
for ident in ['h1-packed-0','h1-packed-711','h1-packed-7237','h1-gram-heavy']:
 src=R/'measurements'/ident/'export.ndjson';out=R/'measurements'/ident
 rec=run([TC/'leanchecker','--from-export',src],out,'lean-replay',ENV,600,7)
 rec['accepts']=rec['exit']==0 and 'Lean default kernel accepts the solution' in (out/'lean-replay.log').read_text()
 rr.append(dict(sample=ident,**rec))
(R/'lean-replay-results.json').write_text(json.dumps(rr,indent=2))
