from pathlib import Path
import re,json
from fractions import Fraction as F
root=Path(__file__).resolve().parents[1]
rows=json.load(open(root/'logs/h3_parity_summary.json'));out=[]
for r in rows:
 if not r['valid_prefix']:continue
 stem=r['name'];names=[(stem+'_B_free',1),(stem+'_C_free',1)]+[(stem+'_B_d1',1),(stem+'_B_d2',1)]+[(stem+'_C_d'+str(d),1) for d in [1,2,3]]
 profiles=[];complete=True
 for name,mult in names:
  f=root/'logs'/f'{name}.err'
  if not f.exists():
   # Identical mode A was reused from another T at the same m,L,K.
   matches=list((root/'logs').glob(re.sub(r'_T\d+_',r'_T*_',name)+'.err'))
   if not matches:complete=False;continue
   f=matches[0]
  text=f.read_text();mo=re.search(r'PROFILE dfsnodes=(\d+) leaves=(\d+) closed=(\d+) sortpasses=(\d+) steps=(\d+) edges_s=(\d+) edges_t=(\d+) edges_r=(\d+) sites=(\d+) cpu=([\d.]+) maxrss_bytes=(\d+)',text)
  if mo is None:complete=False;continue
  vals=list(mo.groups());vals=[int(x) for x in vals[:9]]+[float(vals[9]),int(vals[10])]
  profiles.append(vals)
 if not complete:continue
 totalsteps=sum(p[4] for p in profiles);ds=sum(p[0] for p in profiles);closed=sum(p[2] for p in profiles)
 sites=profiles[0][8];es,et,er=profiles[0][5:8];nw=sum(1 for l in open(root/'data'/f"windows_m{r['m']}_min.txt")) if 'min' in stem else None
 if 'min' in stem:nw=int(open(root/'data'/f"windows_m{r['m']}_min.txt").readline().split()[1])
 else:nw={6:916,8:7500,9:21268,10:60092}.get(r['m'])
 r.update(steps_total=totalsteps,dfs_nodes=ds,closed_calls=closed,transition_site_visits=totalsteps*sites*(es+et+er),float_arithmetic_nominal=totalsteps*sites*(10*(es+et)+8*er),sites=sites,nw=nw,vector_entries=4*nw*sites,two_buffer_bytes=32*nw*sites,maxrss=max(p[10] for p in profiles),cpu_sum=sum(p[9] for p in profiles),edges=[es,et,er])
 out.append(r)
(root/'logs/h3_final_stats.json').write_text(json.dumps(out,indent=2))
for r in sorted(out,key=lambda x:x['transition_site_visits']):
 if r['rho_parity']<1:print(r['name'],r['rho_parity'],r['transition_site_visits'],r['float_arithmetic_nominal'],r['dfs_nodes'])
