from pathlib import Path
from fractions import Fraction as F
import json,re
root=Path(__file__).resolve().parents[1];out=[]
for f in (root/'logs').glob('stationary_*_m*_R*_d*.out'):
 t=f.read_text();mo=re.search(r'DYADIC_FINAL exact=(\w+) bound ([0-9.eE+-]+) ratio ([0-9.eE+-]+)',t)
 if not mo:continue
 X,m,R,d=re.search(r'stationary_([BC])_m(\d+)_R(\d+)_d(\d+)',f.name).groups();check=re.search(r'EXACT_CHECK inequalities=(\d+) bad=(\d+) outside_cap_failures=(\d+) integer_products=(\d+)',t);prof=re.search(r'PROFILE nw=(\d+) sites=(\d+) edges=\d+ state_values=(\d+) bytes=(\d+) maxrss_bytes=(\d+) cpu=([\d.]+)',t)
 if not check or not prof:continue
 out.append(dict(name=f.stem,X=X,m=int(m),L=int(m)+2,R=int(R),d=int(d),bound=mo[2],ratio=mo[3],exact=mo[1],inequalities=int(check[1]),bad=int(check[2]),cap_fail=int(check[3]),products=int(check[4]),nw=int(prof[1]),sites=int(prof[2]),entries=int(prof[3]),bytes=int(prof[4]),maxrss=int(prof[5]),cpu=float(prof[6])))
main=[r for r in out if r['m']==10 and r['R']==70 and 'coarse' not in r['name']];rr={}
for X in ['B','C']:
 vals=[r for r in main if r['X']==X]
 if len(vals)==(2 if X=='B' else 3):
  bound=sum((F(r['bound'])*(2 if X=='B' and r['d']==1 else 1) for r in vals),F(0));h=F(1) if X=='B' else F.from_float(1.20);rr[X]=dict(sum=str(bound),row_bound=float(bound),ratio=float(bound/h))
result=dict(cases=out,main_rows=rr,total_inequalities=sum(r['inequalities'] for r in main),total_integer_products=sum(r['products'] for r in main),cpu_sum=sum(r['cpu'] for r in main),maxrss=max([r['maxrss'] for r in main] or [0]))
(root/'logs/stationary_summary.json').write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2))
