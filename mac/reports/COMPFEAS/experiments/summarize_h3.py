import re,json
from pathlib import Path
from fractions import Fraction as F
root=Path(__file__).resolve().parents[1]
def read(name):
 fn=root/'logs'/f'{name}.out'
 if not fn.exists(): return None
 txt=fn.read_text();E={};D={};rem=None
 for l in txt.splitlines():
  p=l.split()
  if p and p[0] in ['E','D','F']: (E if p[0]=='E' else D)[int(p[1])]=F(p[2])
  if l.startswith('# remainder:'):
   rem=F(re.search(r'remainder<=([0-9.eE+-]+)',l)[1])
   lam=float(re.search(r'lcheck=([0-9.eE+-]+)',l)[1])
   if lam>=1 or 'check=FAILED' in l: return None
  if l.startswith('# TAIL'): tail=F(re.search(r'<= ([0-9.eE+-]+)',l)[1])
 if '# TAIL' not in txt:return None
 return E,D,tail,rem
configs=[]
for f in (root/'logs').glob('h3_*_B_free.out'):
 stem=f.stem[:-7]
 ty,m,L,K,T=re.search(r'h3_(\w+)_m(\d+)_L(\d+)_K(\d+)_T(\d+)',stem).groups();m,L,K,T=map(int,(m,L,K,T))
 rows={};nfiles=0
 for X,h in [('B',F(1)),('C',F.from_float(1.20) if ty.startswith('typed') else F.from_float(1.23))]:
  short=F(0);mid=F(0);ok=True
  for d,mult in ([(1,2),(2,1)] if X=='B' else [(1,1),(2,1),(3,1)]):
   rr=read(stem+f'_{X}_d{d}')
   if rr is None:ok=False;break
   E,D,tail,rem=rr
   short+=mult*sum(E.values())
   mid+=mult*sum(v for n,v in D.items() if L<n<=4*K-5)
  free=read(stem+f'_{X}_free')
  if not ok or free is None:continue
  E,D,tail,rem=free
  # Instead of trusting tail rounded total, add individual printed terms upward plus printed remainder.
  long=sum(v for n,v in D.items() if n>4*K-5)+rem
  rows[X]=dict(short=float(short),mid=float(mid),long=float(long),rem=float(rem),ratio=float((short+mid+long)/h))
 if len(rows)==2:
  configs.append(dict(name=stem,m=m,L=L,K=K,T=T,rows=rows,rho=max(r['ratio'] for r in rows.values())))
print(json.dumps(sorted(configs,key=lambda r:(r['m'],r['L'],r['K'],r['name'])),indent=2))
