from fractions import Fraction as F
from pathlib import Path
from decimal import Decimal,localcontext

def dec(q):
    with localcontext() as c:
        c.prec=35
        return str(Decimal(q.numerator)/Decimal(q.denominator))

h,S={},{}
for line in Path('audit/h2_integer_certificate.tsv').read_text().splitlines():
    f=line.split()
    if f[0]=='h':
        h[int(f[1])]=int(f[2]);S.setdefault(int(f[1]),[])
    if f[0]=='S':
        row,a,t,r,v=map(int,f[1:]);S.setdefault(row,[]).append((a,t,r,v))
assert len(h)==len(S)==938 and min(h.values())>0
ratio=F(max(h.values()),min(h.values()))
assert ratio<=100
lam,arg=max((sum((v*F(1000,2883)**a*F(200,561)**t*F(1,4)**r for a,t,r,v in row),F(0))/h[i],i) for i,row in S.items())
print('orbits=',len(h),'hmax/hmin=',ratio,'argmax code=',arg)
print('exact lambda=',lam)
print('lambda decimal=',dec(lam))
print('lambda <= .8559487104:',lam<=F('.8559487104'))
print('.85594872 < (3923/4000)^8:',F('.85594872')<F(3923,4000)**8)
print('(3923/4000)^8=',dec(F(3923,4000)**8))
assert lam<=F('.8559487104')<F('.85594872')<F(3923,4000)**8
print('lambda > .9807^8:',lam>F('.9807')**8)
assert lam>F('.9807')**8
# A second instance is generated with revisit 1/5; it must choose its own vector.
