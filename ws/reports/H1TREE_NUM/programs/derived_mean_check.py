"""Certify the extra, usually sharper, means used by our enumeration."""
import sympy as s
from common import *
from exact_check import bernstein

rows=[];x,y,z=s.symbols('x y z')
audit=json.loads((ROOT/'data/geometry_audit.json').read_text())
for case in audit['mean_triples']:
    rr=sorted(map(s.Rational,case['radii']));rr=[s.Rational(0)]*(3-len(rr))+rr
    a,b,c=rr;R=s.Rational(case['R'])
    if case['law']=='u' and b==c==1:
        alpha=a*(2*y-1);d=2+2*x*x
        gap=25*R*R*(d+2*x*alpha)**2-(2*d*alpha+10*x)**2-(d+2)**2*(a*a-alpha*alpha)
        bb=bernstein(gap,(x,y),4);method='unit-pair'
    else:
        ab=a*b*(1-2*x);ac=a*c*(1-2*y);bc=b*c*(1-2*z)
        gram=s.Matrix([[a*a,ab,ac],[ab,b*b,bc],[ac,bc,c*c]])
        v=s.Matrix([5+bc,5+ac,5+ab]);d=3 if case['law']=='u' else 5
        gap=25*R*R*(d+ab+ac+bc)**2-(v.T*gram*v)[0]
        bb=bernstein(gap,(x,y,z),2);method='cube'
    rows.append(dict(**case,method=method,coefficient_count=len(bb),minimum=str(min(bb)),verified=min(bb)>=0))
result=dict(cases=len(rows),coefficient_count=sum(r['coefficient_count'] for r in rows),failures=[r for r in rows if not r['verified']],results=rows)
dump('data/derived_mean_checks.json',result)
print(json.dumps({k:v for k,v in result.items() if k!='results'}))
