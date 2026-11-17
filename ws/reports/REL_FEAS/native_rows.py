import sys,json
sys.path.insert(0,'/home/ubuntu/aklt/reports/REL_FEAS')
from measure import *
env=ENV.copy();env['LEAN_PATH']=str(ST)+':'+LP
out=R/'measurements/h3-row-group';out.mkdir(parents=True,exist_ok=True)
mods=[s['module'] for s in samples() if s['id'].startswith('h3-row-')]
roots=[n for mod in mods for n in globals()['roots'](ST/(mod.replace('.','/')+'.lean'))]
(ST/'RELFEAS/Rows.lean').write_text('\n'.join('import '+m for m in mods)+'\n')
r=dict(id='h3-row-group',module='RELFEAS.Rows',modules=mods,roots=roots,family='H3',
       lean_individual_seconds=[7.46,8.25,8.86],conversion=None)
(out/'roots.txt').write_text('\n'.join(roots)+'\n')
run([TC/'lean','-o',ST/'RELFEAS/Rows.olean',ST/'RELFEAS/Rows.lean'],out,'import',env,120,22)
r['export']=run([R/'fast-leanexport','RELFEAS.Rows','--',*roots],out,'export',env,1800,22)
if r['export']['exit']==0:
 e=out/'export.ndjson';(out/'export.log').rename(e);r['export_bytes']=e.stat().st_size;r['export_sha256']=sha(e)
 cfg=dict(export_file_path=str(e),permitted_axioms=['propext','Classical.choice','Quot.sound'],
  unpermitted_axiom_hard_error=True,nat_extension=True,string_extension=True,print_success_message=True,num_threads=1)
 (out/'nanoda-config.json').write_text(json.dumps(cfg))
 for tag,cmd in [('conron',[TC/'con-ron','--verified','--jobs=1','--progress=1',e]),
                 ('nanoda',[TC/'nanoda_bin',out/'nanoda-config.json'])]:
  r[tag]=run(cmd,out,tag,env,900,20)
  t=(out/(tag+'.log')).read_text(errors='replace')
  r[tag]['accepts']=r[tag]['exit']==0 and ('declarations (--verified)' in t if tag=='conron' else 'no typechecker errors' in t)
(out/'result.json').write_text(json.dumps(r,indent=2))
