import sys,json,importlib.util
sys.path.insert(0,'/home/ubuntu/aklt/reports/REL_FEAS')
from measure import *
spec=importlib.util.spec_from_file_location('release_runner',WT/'release/release.py');mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
env=ENV.copy();env['LEAN_PATH']=str(ST)+':'+LP
p=ST/'RELFEAS/AuditFixture.lean'
p.write_text('''import Init
namespace RELFEAS.AuditFixture
def Goal : Prop := True
class Witness : Prop where ok : True
instance : Witness := ⟨True.intro⟩
theorem closed : Goal := True.intro
theorem conditional [Witness] : Goal := True.intro
example : Goal := conditional
end RELFEAS.AuditFixture
''')
out=R/'measurements/AuditGuard';r={}
r['build']=run([TC/'lean','-o',p.with_suffix('.olean'),p],out,'build',env,120,4)
for name in ['closed','conditional']:
 q=ST/('RELFEAS/Audit_'+name+'.lean')
 q.write_text(mod.audit_source('RELFEAS.AuditFixture','RELFEAS.AuditFixture.'+name,'RELFEAS.AuditFixture.Goal',False))
 r[name]=run([TC/'lean',q],out,name,env,120,4)
r['pass']=r['build']['exit']==0 and r['closed']['exit']==0 and r['conditional']['exit']!=0 and 'target declaration type differs from the closed headline' in (out/'conditional.log').read_text()
r['runner_sha256']=sha(WT/'release/release.py')
(out/'result.json').write_text(json.dumps(r,indent=2))
if not r['pass']:raise SystemExit('audit guard test failed')
