import sys,json
sys.path.insert(0,'/home/ubuntu/aklt/reports/REL_FEAS')
import measure as m
ss=[s for s in m.samples() if s['id'].startswith('h3-row-')]
m.prepare(ss)
# Build three original row modules, then one full-closure checker/export measurement.
env=m.ENV.copy();env['LEAN_PATH']=str(m.ST)+':'+m.LP
for s in ss[1:]:
 out=m.R/'measurements'/s['id'];src=m.ST/(s['module'].replace('.','/')+'.lean')
 roots=m.roots(src);out.mkdir(parents=True,exist_ok=True);(out/'roots.txt').write_text('\n'.join(roots)+'\n')
 r=dict(s,roots=roots)
 r['lean']=m.run([m.TC/'lean','-DautoImplicit=false','-DrelaxedAutoImplicit=false','-DElab.async=false','-o',src.with_suffix('.olean'),src],out,'lean',env,300,22)
 (out/'kernel-only.json').write_text(json.dumps(r,indent=2))
orig=m.run
def run(cmd,out,tag,env,seconds=180,rss_gib=22):
 if tag=='export':seconds=1800
 if tag in ['conron','nanoda']:seconds=600
 return orig(cmd,out,tag,env,seconds,rss_gib)
m.run=run
r=m.measure(ss[0]);(m.R/'row-result.json').write_text(json.dumps(r,indent=2))
