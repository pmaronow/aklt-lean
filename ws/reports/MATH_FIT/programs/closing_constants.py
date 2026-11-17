import json
from fractions import Fraction as F
from pathlib import Path
H=F(6,5);C=F(18094,100000)+2*F(36751,100000);rho0=F(967725,10**6);rho=(1+rho0)/2;rows=[]
for name,q,CV in [('retained_H2',F(1119948287353,1120437614225),10),('folded_H2',F(7999,8000),16000)]:
 b=(1+q)/2;r=q/b;B=2*H*C*CV/b**2*r/(1-r)**3;eps=min((1-b)/2,(1-rho0)/(2*B));theta=1-eps;CT=2*F(12,5)**24*(CV/(1-q))**2;A=H*max(2,CT)/(1-rho)
 assert 0<q*q<q<b<theta<1 and rho0<rho<1 and eps*B<=(1-rho0)/2
 rows.append(dict(name=name,q=str(q),CV=CV,epsilon=str(eps),epsilon_float=float(eps),CT_float=float(CT),A_float=float(A),rho=str(rho),inequalities_checked=True))
Path('data/closing_constants.json').write_text(json.dumps(rows,indent=2));print(json.dumps(rows,indent=2))
