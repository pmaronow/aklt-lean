import sys,json,math,itertools
from fractions import Fraction as F
sys.path.insert(0,'programs');from mean_bernstein import con,linear,add,mul,sq,scale,bernstein
rows=[]
for r in [F(1,25),F(1,10),F(3,25)]:
 T=linear(F(0),F(1),0);alpha=linear(-r,2*r,1);d=add(con(2),scale(sq(T),2));R=(5+4*r)/(10+5*r)
 # The S=(b+c), D=(b-c) decomposition eliminates the Gram constraint.
 den=add(d,scale(mul(T,alpha),2));nume=add(sq(add(scale(mul(d,alpha),2),scale(T,10))),mul(sq(add(d,con(2))),add(con(r*r),scale(sq(alpha),-1))))
 P=add(scale(sq(den),25*R*R),scale(nume,-1))
 for n in [4,5,6,8,10,12]:
  b=bernstein(P,n)
  if min(b.values())>=0:break
 row=dict(r=str(r),R=str(R),degree=n,min=str(min(b.values())),success=min(b.values())>=0,max_bits=max(max(abs(v.numerator).bit_length(),v.denominator.bit_length()) for v in b.values()),nonzero=sum(bool(v) for v in b.values()));rows.append(row)
print(json.dumps(rows,indent=2));open('data/mean_unit_pair.json','w').write(json.dumps(rows,indent=2))
