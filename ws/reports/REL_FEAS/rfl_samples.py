import sys,json
sys.path.insert(0,'/home/ubuntu/aklt/reports/REL_FEAS')
import measure as m
ss=[]
for ident,orig in [('RflRaw','CertData.H3.Check.Raw.R0063'),('RflPrefix','CertData.H3.B1.Check.Prefix.P0106')]:
 mod='RELFEAS.'+ident
 p=m.ST/(orig.replace('.','/')+'.lean');txt=p.read_text()
 txt=txt.replace('namespace '+orig,'namespace '+mod).replace('end '+orig,'end '+mod)
 txt=txt.replace('by decide +kernel','by exact Eq.refl expected').replace('maxHeartbeats 0','maxHeartbeats 1000000000')
 (m.ST/'RELFEAS'/f'{ident}.lean').write_text(txt)
 ss.append(dict(id=ident.lower(),module=mod,family='H3',conversion='Eq.refl expected instead of decide +kernel',original_module=orig))
original=m.run
def run(cmd,out,tag,env,seconds=180,rss_gib=22):
 if tag in ['conron','nanoda']:seconds=600
 return original(cmd,out,tag,env,seconds,rss_gib)
m.run=run
for s in ss:
 r=m.measure(s)
 with (m.R/'rfl-samples.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
