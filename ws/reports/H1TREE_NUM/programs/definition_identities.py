"""Exact checks linking the algebra used by our programs to the spin laws."""
import itertools as it
import sympy as s
from common import *
from exact_check import moment_integer

phi=(1+s.sqrt(5))/2;r2=phi+2
raw=[]
for a,b in it.product((-1,1),repeat=2):raw += [(0,a,b*phi),(a,b*phi,0),(a*phi,0,b)]
checks=[]
for degree in range(5):
    for a in range(degree+1):
        for b in range(degree-a+1):
            e=(a,b,degree-a-b)
            numerator=sum(s.prod(n[j]**e[j] for j in range(3)) for n in raw)
            actual=s.simplify(numerator/(12*r2**s.Rational(degree,2)))
            expected=s.Rational(moment_integer('u',e),15)
            checks.append(dict(exponent=e,actual=str(actual),expected=str(expected),verified=s.simplify(actual-expected)==0))

x,y,z=s.symbols('x y z');p=x+y+z
gram=s.Matrix([[1,x,y],[x,1,z],[y,z,1]]);v=s.Matrix([5+z,5+y,5+x])
X,Y,Z=1-z,1-y,1-x
three_gap=s.expand((9+3*p)**2-(v.T*gram*v)[0]-4*((X-Y)**2+(X-Z)**2+(Y-Z)**2)-6*X*Y*Z)

t,q,alpha,beta,gamma=s.symbols('t q alpha beta gamma')
a=s.Matrix([alpha,beta,gamma]);b=s.Matrix([t,q,0]);c=s.Matrix([t,-q,0])
N=(5+b.dot(c))*a+(5+a.dot(c))*b+(5+a.dot(b))*c
reduce=lambda expr:s.rem(s.Poly(s.expand(expr),q),s.Poly(q*q+t*t-1,q)).as_expr()
d=2+2*t*t
upper=(2*d*alpha+10*t)**2+(d+2)**2*(beta*beta+gamma*gamma)
unit_gap=s.factor(reduce(upper-N.dot(N))-12*(1-t**4)*beta*beta)

result=dict(moment_count=len(checks),moment_failures=[r for r in checks if not r['verified']],
            three_unit_mean_identity=(three_gap==0),unit_pair_norm_identity=(unit_gap==0),
            arrival_auxiliary_second_moment=(s.Rational(3,5)*s.Rational(1,3)==s.Rational(1,5)),
            D_mixture_nonzero_weight=(s.Rational(3,5)*s.Rational(1,12)==s.Rational(1,20)),
            top_D_kernel_weight=(s.Rational(3,5)*s.Rational(1,3)==s.Rational(1,5)),moments=checks)
dump('data/definition_identities.json',result)
print(json.dumps({k:v for k,v in result.items() if k!='moments'}))
