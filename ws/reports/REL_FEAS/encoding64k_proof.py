import sys,json
sys.path.insert(0,'/home/ubuntu/aklt/reports/REL_FEAS')
from measure import *
p=ST/'RELFEAS/ShiftEncoding64K.lean';p.write_text((ST/'RELFEAS/ShiftEncoding.lean').read_text().replace('ShiftEncoding','ShiftEncoding64K').replace('8192','65536').replace('8191','65535'))
env=ENV.copy();env['LEAN_PATH']=str(ST)+':'+LP
q=run([TC/'lean','-o',p.with_suffix('.olean'),p],R/'measurements/ShiftEncoding64K','lean',env,120,4)
(R/'measurements/ShiftEncoding64K/result.json').write_text(json.dumps(dict(lean=q),indent=2))
