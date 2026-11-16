import json,re
from pathlib import Path
root=Path(__file__).resolve().parents[1]
a=json.load(open(root/'logs/h1_chol_summary.json'));b=json.load(open(root/'logs/h1_chol_extra_summary.json'))
combine={k:(max(a['stats'][k],b['stats'][k]) if k.startswith('max_') else a['stats'][k]+b['stats'][k]) for k in a['stats']}
raw=r'PROFILE dfsnodes=(\d+) leaves=(\d+) closed=(\d+) sortpasses=(\d+) steps=(\d+) edges_s=(\d+) edges_t=(\d+) edges_r=(\d+) sites=(\d+) cpu=([\d.]+) maxrss_bytes=(\d+)'
mem=[]
for f in (root/'logs').glob('*.err'):
 for m in re.finditer(raw,f.read_text()):mem.append((int(m[11]),f.name))
base=dict(windows=60092,sites=1568,phases=4,steps=925,edges=[54124,108248,6720])
base['entries']=base['windows']*base['sites']*4;base['two_buffers']=base['entries']*8
es,et,er=base['edges'];base['transition_site_visits']=925*1568*(es+et+er);base['generic_float_ops']=925*1568*(10*(es+et)+8*er)
result=dict(h1_all_gram=combine,h1_all_gram_wall=a['wall']+b['wall'],h3_paper_baseline=base,max_c_rss=max(mem),max_profile_rss_top=sorted(mem,reverse=True)[:5])
(root/'logs/report_numbers.json').write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2))
