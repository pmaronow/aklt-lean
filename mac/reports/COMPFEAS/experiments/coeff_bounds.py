from fractions import Fraction as F
import json
from pathlib import Path
root=Path(__file__).resolve().parents[1]
def bounds(s,N=8):
 t=(1-s)/(1+s)
 lo=2*sum((t**(2*k+1)/F(2*k+1) for k in range(N)),F(0))/(1-s)
 err=2*t**(2*N+1)/(F(2*N+1)*(1-t*t)*(1-s))
 return lo,lo+err
rows=[]
lJ,uJ=bounds(F(116,125))
for c,aa,bb,pp in [(F(961,1000),F(145217,10**6),F(352782,10**6),F(340008,10**6)),(F(187,200),F(150000,10**6),F(357549,10**6),F(344661,10**6))]:
 li,ui=bounds(F(116,125)*c);lp,up=bounds(c)
 a=ui/3-lJ/5;b=ui/3;p=up/3
 assert a<aa and b<bb and p<pp
 rows.append(dict(c=str(c),alpha_upper=str(a),beta_upper=str(b),beta_prime_upper=str(p),alpha_float=float(a),beta_float=float(b),beta_prime_float=float(p),targets=[str(aa),str(bb),str(pp)],ok=True))
(root/'logs/coeff_bounds.json').write_text(json.dumps(rows,indent=2));print(json.dumps(rows,indent=2))
