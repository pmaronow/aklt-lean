import json,math
from fractions import Fraction as F
from pathlib import Path
S=2**40
v={int(code):max(1,int(round(float(value)*S))) for code,value in (l.split() for l in Path('data/h2_best_uniform.tmp').read_text().splitlines())}
# Give the one-step test even stronger constants than the sharp refined local limits.
cs=F(963,1000);ct=F(117,125);ws=1/(3*cs);wt=1/(3*ct);wr=F(1,5);m=4;dx=[1,0,-1,0];dy=[0,1,0,-1];ratios=[];edges=0
for code,vi in v.items():
 ds=[(code//(4**i))%4 for i in range(m)];p=(0,0);depart=set();used=set()
 for d in ds:
  q=(p[0]+dx[d],p[1]+dy[d]);used.add(tuple(sorted([p,q])));depart.add(p);p=q
 row=F(0)
 for d in range(4):
  q=(p[0]+dx[d],p[1]+dy[d]);ed=tuple(sorted([p,q]))
  if ed in used:continue
  nc=code//4+d*4**(m-1);assert nc in v
  row+=(wr if p in depart else ws if d==ds[-1] else wt)*v[nc];edges+=1
 ratios.append(row/vi)
lo=min(ratios);hi=max(ratios);assert lo>F(102,100)
r=dict(states=len(v),edges=edges,cs=str(cs),ct=str(ct),lower=str(lo),lower_float=float(lo),upper=str(hi),upper_float=float(hi),vector_bits=max(x.bit_length() for x in v.values()),argument='A v >= lower v > v rules out A u <= q u for any u>0 and q<1 by a maximal v/u coordinate.')
Path('data/h2_m4_obstruction.json').write_text(json.dumps(r,indent=2));print(json.dumps(r,indent=2))
