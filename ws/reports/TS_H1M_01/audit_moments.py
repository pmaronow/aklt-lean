"""Exact Q(phi) diagnostic of all degree-at-most-four monomial moments."""
from fractions import Fraction as F
from itertools import product
import json
from pathlib import Path


def add(x, y):
    return (x[0]+y[0], x[1]+y[1])


def mul(x, y):
    # phi^2 = phi + 1
    a, b = x
    c, d = y
    return (a*c+b*d, a*d+b*c+b*d)


def power(x, n):
    r = (F(1), F(0))
    for _ in range(n):
        r = mul(r, x)
    return r


def inverse(x):
    a, b = x
    norm = a*a+a*b-b*b
    return ((a+b)/norm, -b/norm)


zero, one, phi = (F(0), F(0)), (F(1), F(0)), (F(0), F(1))
vertices = []
for axis, sign_a, sign_b in product(range(3), (-1, 1), (-1, 1)):
    a = mul((F(sign_a), F(0)), one)
    b = mul((F(sign_b), F(0)), phi)
    vertices.append((zero, a, b) if axis == 0 else
                    (a, b, zero) if axis == 1 else (b, zero, a))
for v in vertices:
    squared = zero
    for coordinate in v:
        squared = add(squared, power(coordinate, 2))
    assert squared == (F(2), F(1))  # icoRadius^2 = phi + 2

checked = 0
for exponents in product(range(5), repeat=3):
    degree = sum(exponents)
    if degree > 4:
        continue
    numerator = zero
    for v in vertices:
        monomial = one
        for coordinate, exponent in zip(v, exponents):
            monomial = mul(monomial, power(coordinate, exponent))
        numerator = add(numerator, monomial)
    if degree % 2:
        assert numerator == zero
        moment = zero
    else:
        denominator = mul((F(12), F(0)), power((F(2), F(1)), degree//2))
        moment = mul(numerator, inverse(denominator))
    expected = (F(1) if degree == 0 else F(1, 3) if degree == 2 and 2 in exponents
                else F(1, 5) if degree == 4 and 4 in exponents
                else F(1, 15) if degree == 4 and all(e % 2 == 0 for e in exponents)
                else F(0))
    assert moment == (expected, F(0)), (exponents, moment, expected)
    diluted = add(mul((F(3, 5), F(0)), moment),
                   (F(2, 5), F(0)) if degree == 0 else zero)
    assert diluted == ((expected if degree == 0 else F(3, 5)*expected), F(0))
    checked += 1
result = dict(result='PASS', monomials=checked, statuses=2, unit_vertices=12,
              arithmetic='exact Q(phi), phi^2=phi+1')
Path(__file__).with_name('moments-check.json').write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps(result, sort_keys=True))
