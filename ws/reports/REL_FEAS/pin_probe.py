import sys,json,importlib.util
sys.path.insert(0,'/home/ubuntu/aklt/reports/REL_FEAS')
from measure import *
spec=importlib.util.spec_from_file_location('release_gate','/home/ubuntu/aklt/wt/REL_FEAS/release/release.py')
gate=importlib.util.module_from_spec(spec);spec.loader.exec_module(gate)
env=ENV.copy();env['LEAN_PATH']=str(ST)+':'+LP
out=R/'measurements/probe-ShiftLeftPins'
r={'module':'RELFEAS.ShiftLeft','roots':gate.PRIMS+['RELFEAS.ShiftLeft.checked']}
r['export']=run([TC/'leanexport',r['module'],'--',*r['roots']],out,'export',env,90,8)
e=out/'export.ndjson';(out/'export.log').rename(e)
r['conron']=run([TC/'con-ron','--verified','--jobs=1','--progress=1',e],out,'conron',env,120,6)
r['conron']['accepts']=r['conron']['exit']==0 and 'declarations (--verified)' in (out/'conron.log').read_text()
(out/'result.json').write_text(json.dumps(r,indent=2))
