import math,json
from fractions import Fraction as F
q=F(1119948287353,1120437614225);rho=F(993015,10**6);H=F(5404319552844595,4503599627370496);C=F(18094,100000)+2*F(36751,100000);CV=10
b=(1+q)/2;r=q/b;B=2*H*C*CV/b**2*r/(1-r)**3
eps=min((1-b)/2,(1-rho)/(2*B));CT=2*F(12,5)**24*(CV/(1-q))**2;A=H*max(2,CT)/((1-rho)/2)
f=lambda s: -math.log(s)/(1-s)
rows=[]
for cs,ct in [(.961,.935),(.960,.934),(.95,.925),(.97,.945),(1,1)]:
 coeff=[]
 for c in (cs,ct):
  fa=f(.928);fac=f(.928*c);fc=1 if c==1 else f(c)
  coeff.append(dict(a=fac/3-fa/5,b=fac/3,bp=fc/3))
 rows.append(dict(cs=cs,ct=ct,coeff=coeff))
out=dict(q=float(q),H2_slack=float(1-q),H3_B=.993014271,H3_C=1.181674468/float(H),H3_B_slack=1-.993014271,H3_C_slack=1-1.181674468/float(H),B_star=float(B),epsilon=float(eps),theta_loss=float(eps),C_T=float(CT),A=float(A),coefficients=rows)
open('data/slack.json','w').write(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
