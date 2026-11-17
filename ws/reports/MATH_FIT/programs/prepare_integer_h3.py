import sys,json,math
from fractions import Fraction as F
import numpy as np
from pathlib import Path
m=10;R=70;V=2**20;D=2**48;r=F(12,13);h=F(6,5)
lines=Path('/home/ubuntu/aklt/compfeas/data/windows_m10_min.txt').read_text().splitlines();nraw,nq=map(int,lines[0].split());records=[list(map(int,l.split())) for l in lines[nraw+1:]]
xs=F(1000,961);xt=F(200,187);a=[F(145217,10**6),F(150000,10**6)];b=[F(352782,10**6),F(357549,10**6)];bp=[F(340008,10**6),F(344661,10**6)]
ceil=lambda x:(x.numerator+x.denominator-1)//x.denominator
q3=ceil(D*F(1,3));q5=ceil(D*F(1,5));qs=ceil(D*xs/3);qt=ceil(D*xt/3)
resp=np.zeros((4,4,5),dtype=np.uint64);trueresp={}
dx=[1,0,-1,0];dy=[0,1,0,-1]
for ain in range(4):
 for d in range(4):
  if d==(ain+2)%4:continue
  f,g=[j for j in range(4) if j not in [(ain+2)%4,d]];ty=int(d!=ain);hp=lambda j,k:F(1) if (j-k)%4==2 else h
  for delta in range(5):
   if delta==f:K=bp[ty]*hp(g,d)
   elif delta==g:K=bp[ty]*hp(f,d)
   else:K=a[ty]*hp(f,g)+b[ty]*(hp(f,d)+hp(g,d))
   trueresp[ain,d,delta]=(xs if ty==0 else xt)*K/3;resp[ain,d,delta]=ceil(D*trueresp[ain,d,delta])
zf=np.fromfile('data/cap_axis_slack.bin',dtype=np.float64).reshape(4,4,nq);z=np.ceil(zf*V).astype(np.uint32)
bad=0;minmargin=None
for j,(sx,sy) in enumerate([(1,0),(-1,0),(0,1),(0,-1)]):
 for p in range(4):
  for q,row in enumerate(records):
   ain=row[0]&3;s=0
   for d,t in enumerate(row[1:5]):
    if t<0:continue
    k=row[5+d];tilt=r**(sx*dx[d]+sy*dy[d]);ww=F(1,5) if k==2 else ((xs/3 if k==0 else xt/3) if p==0 else (xs/3 if k==0 and p in [1,2] else F(1,3)))
    s+=ceil(D*ww*tilt)*int(z[j,p,t])
    if (p==0 and k==1) or (p==1 and k==0):s+=ceil(D*trueresp[ain,d,4]*tilt)*int(z[j,2 if p==0 else 3,t])
   margin=D*int(z[j,p,q])-s;bad+=margin<0;minmargin=margin if minmargin is None else min(minmargin,margin)
assert bad==0,(bad,minmargin)
assert np.all(z[:,2:,:]>=V)
# Every cap uses the exact rational r^s; floor and ceiling are used on the two sides of the patch boundary.
Z=z.astype(np.uint64);init=np.empty((2,4,nq,2*R+1),dtype=np.uint32);tails=np.empty((2,4,nq,2),dtype=np.uint32)
for axis in [0,1]:
 for t in range(-R-1,R+2):
  rp=r**t;rm=r**(-t)
  for p in range(4):
   vals=[min(F(int(Z[2*axis,p,q]))*rp,F(int(Z[2*axis+1,p,q]))*rm) for q in range(nq)]
   if abs(t)<=R:init[axis,p,:,t+R]=[v.numerator//v.denominator for v in vals]
   else:tails[axis,p,:,0 if t<0 else 1]=[ceil(v) for v in vals]
assert np.all(init[:,2:,:,R]>=V)
init.tofile('data/line_init_integer.bin');tails.tofile('data/line_tails_integer.bin');z.tofile('data/axis_z_integer.bin')
resptext=',\n'.join('{'+','.join('{'+','.join(str(int(v))+'ULL' for v in rr)+'}' for rr in row)+'}' for row in resp)
Path('programs/h3_integer_weights.h').write_text('#include <stdint.h>\n#define VBITS 20\n#define VSCALE (UINT64_C(1)<<VBITS)\n#define QSCALE (UINT64_C(1)<<48)\nstatic const uint64_t q3='+str(q3)+'ULL,q5='+str(q5)+'ULL,qs='+str(qs)+'ULL,qt='+str(qt)+'ULL;\nstatic const uint64_t qresp[4][4][5]={'+resptext+'};\n')
summary=dict(m=m,Rline=R,states=nq,value_bits=20,weight_bits=48,ratio=str(r),hC=str(h),tilted_rows=16*nq,tilted_failures=bad,minimum_tilted_margin=str(minmargin),z_max=int(z.max()),cap_max=int(init.max()),line_values=int(init.size),max_bits=int(init.max()).bit_length(),weights=dict(q3=q3,q5=q5,qs=qs,qt=qt),line_initial_bytes=init.nbytes)
Path('data/h3_integer_setup.json').write_text(json.dumps(summary,indent=2));print(json.dumps(summary,indent=2))
