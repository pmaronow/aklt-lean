import sys,json
sys.path.insert(0,'/home/ubuntu/aklt/reports/REL_FEAS')
from measure import *
env=ENV.copy();env['LEAN_PATH']=str(ST)+':'+LP
out=R/'measurements/PlaneShiftNative8K';r={}
r['export']=run([R/'fast-leanexport','RELFEAS.PlaneShift','--','Nat.div','Nat.mod','RELFEAS.PlaneShift.checked'],out,'export',env,180,7)
if r['export']['exit']==0:
 p=out/'export.ndjson';(out/'export.log').rename(p);r.update(export_bytes=p.stat().st_size,export_sha256=sha(p));d=json.loads((R/'measurements/PlaneShift/result.json').read_text());r['byte_identical_to_stock_checked_export']=r['export_sha256']==d['export_sha256']
(out/'result.json').write_text(json.dumps(r,indent=2))
