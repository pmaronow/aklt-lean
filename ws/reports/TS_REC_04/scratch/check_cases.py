"""Supplementary finite/numerical checks; these are not proofs of the leaves."""

from fractions import Fraction as Q
from itertools import product
from decimal import Decimal, getcontext
import json
import math
import random


class DecimalMath:
    mpf = staticmethod(Decimal)
    sqrt = staticmethod(lambda x: Decimal(x).sqrt())
    log = staticmethod(lambda x: Decimal(x).ln())
    fprod = staticmethod(lambda xs: math.prod(xs, start=Decimal(1)))


mp = DecimalMath()
getcontext().prec = 350
EPS = mp.mpf('1e-240')
counts = {}


def real(q):
    q = Q(q)
    return mp.mpf(q.numerator) / q.denominator


def dot(a, b):
    return sum(x * y for x, y in zip(a, b))


def add(a, b):
    return tuple(x + y for x, y in zip(a, b))


def mul(t, a):
    return tuple(t * x for x in a)


def unit(a):
    return mul(1 / mp.sqrt(dot(a, a)), a)


phi = (1 + mp.sqrt(5)) / 2
radius = mp.sqrt(phi + 2)
atoms = []
for i, a, b in product(range(3), [-1, 1], [-1, 1]):
    v = [(0, a, b * phi), (a, b * phi, 0), (b * phi, 0, a)][i]
    atoms.append(mul(1 / radius, v))

for exps in product(range(5), repeat=3):
    if sum(exps) > 4:
        continue
    measured = sum(mp.fprod(v[i] ** exps[i] if exps[i] else mp.mpf(1) for i in range(3)) for v in atoms) / 12
    if any(k % 2 for k in exps):
        expected = 0
    elif sum(exps) == 0:
        expected = 1
    elif sum(exps) == 2:
        expected = mp.mpf(1) / 3
    else:
        expected = mp.mpf(1) / (5 if 4 in exps else 15)
    assert abs(measured - expected) < EPS
    counts['moment_monomials'] = counts.get('moment_monomials', 0) + 1


def site(status, fields, observable=lambda n: mp.mpf(1)):
    value = sum(observable(n) * mp.fprod(1 + dot(n, b) for b in fields) for n in atoms) / 12
    return value if status == 'U' else mp.mpf(3) / 5 * value + mp.mpf(2) / 5 * observable((0, 0, 0))


rng = random.Random(4)
for status in ['U', 'D']:
    for k in range(4):
        for trial in range(4):
            fields = []
            for j in range(k):
                if trial == 0:
                    b = (mp.mpf(0),) * 3
                elif trial == 1:
                    b = (mp.mpf(1), mp.mpf(0), mp.mpf(0))
                else:
                    direction = unit(tuple(mp.mpf(rng.randrange(-100, 101)) for _ in range(3)))
                    b = mul(real(Q(rng.randrange(101), 100)), direction)
                fields.append(b)
            A = site(status, fields)
            mu = tuple(site(status, fields, lambda n, j=j: n[j]) / A for j in range(3))
            r = mp.sqrt(dot(mu, mu))
            assert A > 0 and r <= mp.mpf(3) / 5 + EPS
            if r < EPS:
                u, v, q = (mp.mpf(1), 0, 0), (0, mp.mpf(1), 0), -mp.mpf(1) / 2
            else:
                u = mul(1 / r, mu)
                e = tuple(mp.mpf(j == min(range(3), key=lambda i: abs(u[i]))) for j in range(3))
                v = unit(add(e, mul(-dot(e, u), u)))
                lo, hi = -mp.mpf(1) / 2, mp.mpf(1)
                for _ in range(950):
                    q = (lo + hi) / 2
                    path_mean = (4 + 10 * q + 4 * q**2) / (10 * (q*q + q + 1))
                    if path_mean < r:
                        lo = q
                    else:
                        hi = q
                q = (lo + hi) / 2
            side = mp.sqrt(1 - q*q)
            triple = [u, add(mul(q, u), mul(side, v)), add(mul(q, u), mul(-side, v))]
            assert all(abs(dot(b, b) - 1) < EPS for b in triple)
            Ap = site('U', triple)
            scale = Ap / A
            for probe in [(0, 0, 0), (50, -70, 3), (-2, 4, 8)]:
                obs = lambda n: 1 + dot(n, probe)
                assert abs(site('U', triple, obs) - scale * site(status, fields, obs)) < EPS
            counts['tip_cases'] = counts.get('tip_cases', 0) + 1


def lower(s):
    t = (1 - s) / (1 + s)
    return 2 / (1 - s) * sum((t**(2*k+1) / (2*k+1) for k in range(8)), Q(0))


def upper(s):
    t = (1 - s) / (1 + s)
    return lower(s) + 2*t**17 / (17*(1-t*t)*(1-s))


for tq in [Q(1, 10**8), Q(1, 1000), Q(1, 10), Q(1, 2), Q(9, 10), Q(1)-Q(1, 10**12)]:
    t = real(tq)
    remainder = mp.log((1+t)/(1-t)) - 2 * sum(t**(2*k+1)/(2*k+1) for k in range(8))
    assert -EPS <= remainder <= 2*t**17/(17*(1-t*t)) + EPS
    counts['remainder_cases'] = counts.get('remainder_cases', 0) + 1

for s in [Q(1, 10**12), Q(1, 100), Q(1, 2), Q(116, 125), Q(961, 1000), Q(187, 200), Q(1)-Q(1, 10**12)]:
    sr = real(s)
    f = -mp.log(sr)/(1-sr)
    assert real(lower(s))-EPS <= f <= real(upper(s))+EPS
    counts['enclosure_cases'] = counts.get('enclosure_cases', 0) + 1


def inv_mean(x, y):
    return 1/x if x == y else (mp.log(x)-mp.log(y))/(x-y)


for c, x, y, yp in product([Q(3, 5), Q(187, 200), Q(1)], [Q(1, 100), Q(1), Q(10)],
                          [Q(1, 100), Q(1), Q(10)], [Q(1, 100), Q(1), Q(10)]):
    if yp < y:
        continue
    c, x, y, yp = map(real, (c, x, y, yp))
    G = lambda v: inv_mean(c*x, v)/3-inv_mean(x, v)/5
    assert G(yp) <= G(y) + EPS
    counts['monotonicity_cases'] = counts.get('monotonicity_cases', 0) + 1

# All template-to-exterior directions must be precisely the 20 listed slots.
dirs = {'E': (1, 0), 'N': (0, 1), 'W': (-1, 0), 'S': (0, -1)}
T = {(x, y) for x in range(-2, 3) for y in range(-2, 3) if abs(x)+abs(y) <= 2}
tips = {(2, 0), (0, 2), (-2, 0), (0, -2)}
corners = {(1, 1), (-1, 1), (-1, -1), (1, -1)}
listed = [((1,1),'E'), ((1,1),'N'), ((-1,1),'N'), ((-1,1),'W'),
          ((-1,-1),'W'), ((-1,-1),'S'), ((1,-1),'S'), ((1,-1),'E'),
          ((2,0),'E'), ((2,0),'N'), ((2,0),'S'), ((0,2),'E'), ((0,2),'N'), ((0,2),'W'),
          ((-2,0),'N'), ((-2,0),'W'), ((-2,0),'S'), ((0,-2),'E'), ((0,-2),'W'), ((0,-2),'S')]
actual = {(z, d) for z in T for d, step in dirs.items() if add(z, step) not in T}
assert set(listed) == actual and len(listed) == len(set(listed)) == 20
assert all(sum(z == w for w, _ in listed) == 2 for z in corners)
assert all(sum(z == w for w, _ in listed) == 3 for z in tips)
rotations = [lambda z: z, lambda z: (z[1], -z[0]),
             lambda z: (-z[0], -z[1]), lambda z: (-z[1], z[0])]
for rotate, incoming in zip(rotations, ['N', 'E', 'S', 'W']):
    for outgoing, step in dirs.items():
        assert (rotate(step) == dirs[incoming]) == (outgoing == 'N')
        counts['rotation_cases'] = counts.get('rotation_cases', 0) + 1
counts['template_sites'] = len(T)
counts['external_slots'] = len(listed)
print(json.dumps({'result': 'PASS', 'checks': counts, 'decimal_precision': getcontext().prec}, sort_keys=True))
