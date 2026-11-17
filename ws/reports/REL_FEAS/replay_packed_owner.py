import sys,json
sys.path.insert(0,'/home/ubuntu/aklt/reports/REL_FEAS')
from measure import *
ident='h1-packed-owner';out=R/'measurements'/ident
rec=run([TC/'leanchecker','--from-export',out/'export.ndjson'],out,'lean-replay',ENV,600,10)
rec['accepts']=rec['exit']==0 and 'Lean default kernel accepts the solution' in (out/'lean-replay.log').read_text()
p=R/'lean-replay-results.json';rr=json.loads(p.read_text());rr=[r for r in rr if r['sample']!=ident];rr.append(dict(sample=ident,**rec));p.write_text(json.dumps(rr,indent=2))
