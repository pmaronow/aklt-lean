import concurrent.futures,json,sys
sys.path.insert(0,'/home/ubuntu/aklt/reports/REL_FEAS')
from measure import *
e=R/'measurements/h3-row-group/export.ndjson'
cfg=dict(export_file_path=str(e),permitted_axioms=['propext','Classical.choice','Quot.sound'],unpermitted_axiom_hard_error=True,nat_extension=True,string_extension=True,print_success_message=True,num_threads=1)
out=R/'measurements/h3-row-group-long';out.mkdir(parents=True,exist_ok=True)
(out/'nanoda-config.json').write_text(json.dumps(cfg))
commands={'conron':[TC/'con-ron','--verified','--jobs=1','--progress=1',e],'nanoda':[TC/'nanoda_bin',out/'nanoda-config.json']}
def one(tag):
 r=run(commands[tag],out,tag,ENV,5400,20)
 txt=(out/(tag+'.log')).read_text(errors='replace')
 r['accepts']=r['exit']==0 and ('declarations (--verified)' in txt if tag=='conron' else 'no typechecker errors' in txt)
 (out/(tag+'-result.json')).write_text(json.dumps(r,indent=2))
 return tag,r
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
 rr=dict(pool.map(one,commands))
r=dict(id='h3-row-group',family='H3',modules=['CertData.H3.B1.Check.Rows.'+n for n in ['R0233','R0026','R0011']],
 roots=(R/'measurements/h3-row-group/roots.txt').read_text().split(),
 lean={'wall_s':7.46+8.25+8.86,'sampled_peak_bytes':9.133*1024**3},
 lean_individual_seconds=[7.46,8.25,8.86],export=json.loads((R/'measurements/h3-row-group/export.json').read_text()),
 export_bytes=e.stat().st_size,export_sha256=sha(e),**rr)
(out/'result.json').write_text(json.dumps(r,indent=2))
