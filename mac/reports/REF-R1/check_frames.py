"""Exact Q(sqrt(5)) checks, using only Python's standard library.

No numerical design certificate is used: antipodal symmetry handles odd total
degree, and exact field arithmetic handles every monomial of even degree <= 4.
"""
from fractions import Fraction as F
from itertools import product
from collections import Counter

def q(a=0, b=0): return (F(a), F(b))
def add(x,y): return (x[0]+y[0], x[1]+y[1])
def neg(x): return (-x[0], -x[1])
def mul(x,y): return (x[0]*y[0]+5*x[1]*y[1], x[0]*y[1]+x[1]*y[0])
def inv(x):
    den=x[0]*x[0]-5*x[1]*x[1]
    return (x[0]/den, -x[1]/den)
def div(x,y): return mul(x,inv(y))
def power(x,n):
    ans=q(1)
    for _ in range(n): ans=mul(ans,x)
    return ans
def total(xs):
    ans=q()
    for x in xs: ans=add(ans,x)
    return ans
def dot(a,b): return total(mul(x,y) for x,y in zip(a,b))
def cyclic(v): return [v, (v[2],v[0],v[1]), (v[1],v[2],v[0])]
def monomial(v, exps):
    ans=q(1)
    for x,n in zip(v,exps): ans=mul(ans,power(x,n))
    return ans
def oddfact(n):
    ans=1
    for i in range(1,n+1,2): ans*=i
    return ans
def sphere_moment(exps):
    if any(n%2 for n in exps): return q()
    numerator=1
    for n in exps: numerator*=oddfact(n-1)
    return q(F(numerator,oddfact(sum(exps)+1)))

phi=q(F(1,2),F(1,2))
iphi=add(phi,q(-1))
ico=[]
dod=[tuple(q(i) for i in signs) for signs in product((-1,1),repeat=3)]
for s,t in product((-1,1),repeat=2):
    ico += cyclic((q(),q(s),mul(q(t),phi)))
    dod += cyclic((q(),mul(q(s),phi),mul(q(t),iphi)))
assert len(set(ico))==12 and len(set(dod))==20

for name,vertices,radius_squared in (
    ('icosahedron',ico,add(phi,q(2))),('dual dodecahedron',dod,q(3))):
    assert all(dot(v,v)==radius_squared for v in vertices)
    assert {tuple(neg(x) for x in v) for v in vertices}==set(vertices)
    checked=0
    for exps in product(range(6),repeat=3):
        degree=sum(exps)
        if degree>5: continue
        raw_sum=total(monomial(v,exps) for v in vertices)
        if degree%2:
            assert raw_sum==q()
        else:
            moment=div(raw_sum,mul(q(len(vertices)),power(radius_squared,degree//2)))
            assert moment==sphere_moment(exps), (name,exps,moment)
        checked+=1
    print(name+':',checked,'monomials of total degree <= 5 verified exactly')

den=mul(q(3),add(phi,q(2)))
gamma_plus_squared=q(F(1,3),F(2,15))
gamma_minus_squared=q(F(1,3),F(-2,15))
counts=Counter(div(power(dot(a,b),2),den) for a in ico for b in dod)
assert counts=={gamma_plus_squared:120,gamma_minus_squared:120}
# Every dodecahedral direction supports exactly a triangular icosahedral face.
# At the maximum, the unnormalized scalar product equals 1+phi.
face_height=add(q(1),phi)
for b in dod:
    face=[a for a in ico if dot(a,b)==face_height]
    assert len(face)==3
    assert all(dot(face[i],face[j])==phi for i in range(3) for j in range(i))
    assert all(total(a[j] for a in face)==mul(face_height,b[j]) for j in range(3))
print('All 240 cross scalar-product squares verified exactly: 120 of each value')
print('All 20 dodecahedral directions support triangular icosahedral faces')
assert gamma_plus_squared[0]>0
# gamma_plus < 159/200 = .795, and therefore 1-gamma_plus > .205.
bound_difference=add(power(q(F(159,200)),2),neg(gamma_plus_squared))
assert bound_difference[0]>0 and bound_difference[1]<0
assert bound_difference[0]**2 > 5*bound_difference[1]**2
print('Exact bound gamma_plus < 159/200, hence 1-gamma_plus > 41/200')

gp=float(gamma_plus_squared[0])+float(gamma_plus_squared[1])*5**0.5
gm=float(gamma_minus_squared[0])+float(gamma_minus_squared[1])*5**0.5
print('Numerical gamma_plus, gamma_minus:',gp**0.5,gm**0.5)
print('Numerical single-site mu(a)/w(a) for four identical pins at maximal dot:',
      (1+gp**0.5)**4/(16/5))
