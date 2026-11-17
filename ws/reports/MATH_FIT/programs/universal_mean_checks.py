import sys,json,collections,runpy,math,itertools
from fractions import Fraction as F
from pathlib import Path
sys.path.insert(0,'programs');import h1_cores as hc
from mean_bernstein import poly,bernstein
calls=set();old=hc.rho_exact

def logmean(k,rs):
 rs=tuple(sorted(list(rs)+[F(0)]*(3-len(rs))));calls.add((k,rs));return old(k,rs)
hc.rho_exact=logmean
runpy.run_path('programs/h1_universal_final.py',run_name='universal_mean_enumeration')
results=[]
for k,rs in sorted(calls):
 P,R=poly(rs,k);B=bernstein(P,2);assert min(B.values())>=0,(k,rs)
 vals=[B[i] for i in itertools.product(range(3),repeat=3)]
 results.append(dict(kind=k,radii=list(map(str,rs)),R=str(R),degree=2,coefficients=list(map(str,vals)),max_bits=max(max(abs(x.numerator).bit_length(),x.denominator.bit_length()) for x in vals)))
summary=dict(cases=len(results),coefficient_count=27*len(results),max_bits=max(r['max_bits'] for r in results),results=results)
Path('data/universal_mean_checks.json').write_text(json.dumps(summary,indent=2));print(json.dumps({k:v for k,v in summary.items() if k!='results'},indent=2))
