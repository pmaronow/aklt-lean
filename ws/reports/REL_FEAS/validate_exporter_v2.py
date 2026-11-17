import sys,json
sys.path.insert(0,'/home/ubuntu/aklt/reports/REL_FEAS')
from measure import *
env=ENV.copy();env['LEAN_PATH']=str(ST)+':'+LP
results=[]
for k in ['NatMul','IntMul','ShiftRight','Pow','List']:
 mod='RELFEAS.'+k;out=R/'exporter-validation-v2'/k
 rec=run([TC/'lean','--run',ST/'RELFEAS/FastMainV2.lean',mod,'--',mod+'.checked'],out,'fast',env,30,8)
 stock=R/'measurements'/('probe-'+k)/'export.ndjson';fast=out/'fast.log'
 rec.update(module=mod,byte_identical=stock.read_bytes()==fast.read_bytes(),stock_sha256=sha(stock),fast_sha256=sha(fast))
 results.append(rec)
(R/'exporter-validation-v2.json').write_text(json.dumps(results,indent=2))
assert all(r['byte_identical'] for r in results)
