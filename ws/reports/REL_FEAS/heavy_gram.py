import sys,json
sys.path.insert(0,'/home/ubuntu/aklt/reports/REL_FEAS')
import measure as m
ss=[s for s in m.samples() if s['id']=='h1-gram-heavy'];m.prepare(ss)
orig=m.run
def run(cmd,out,tag,env,seconds=180,rss_gib=22):
 if tag=='export':cmd=[m.R/'fast-leanexport',*cmd[3:]]
 return orig(cmd,out,tag,env,seconds,rss_gib)
m.run=run
r=m.measure(ss[0]);(m.R/'heavy-gram-result.json').write_text(json.dumps(r,indent=2))
