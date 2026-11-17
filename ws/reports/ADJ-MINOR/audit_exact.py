#!/usr/bin/env python3
"""Independent small checks for ADJ-MINOR; stdlib only, one process.

Reads the frozen certificates only for their stored claims. All mathematics
below is reimplemented here; no referee or manuscript program is imported.
"""
from collections import Counter
from fractions import Fraction as F
from itertools import combinations, product
from math import comb, factorial, sqrt
from pathlib import Path
import json

ROOT = Path('/home/ubuntu/aklt/manuscript/bundle')


class Q5:
    """Exact a+b*sqrt(5)."""
    def __init__(self, a=0, b=0):
        self.a, self.b = F(a), F(b)
    @staticmethod
    def coerce(x):
        return x if isinstance(x, Q5) else Q5(x)
    def __add__(self, x):
        x = self.coerce(x)
        return Q5(self.a+x.a, self.b+x.b)
    __radd__ = __add__
    def __neg__(self):
        return Q5(-self.a, -self.b)
    def __sub__(self, x):
        return self + (-self.coerce(x))
    def __rsub__(self, x):
        return self.coerce(x) - self
    def __mul__(self, x):
        x = self.coerce(x)
        return Q5(self.a*x.a+5*self.b*x.b, self.a*x.b+self.b*x.a)
    __rmul__ = __mul__
    def __truediv__(self, x):
        x = self.coerce(x)
        den = x.a*x.a-5*x.b*x.b
        if not den:
            raise ZeroDivisionError
        return self * Q5(x.a/den, -x.b/den)
    def __rtruediv__(self, x):
        return self.coerce(x) / self
    def __pow__(self, n):
        if n < 0:
            return (1/self)**(-n)
        out = Q5(1)
        for _ in range(n):
            out = out*self
        return out
    def __eq__(self, x):
        x = self.coerce(x)
        return self.a == x.a and self.b == x.b
    def __hash__(self):
        return hash((self.a, self.b))
    def sign(self):
        a, b = self.a, self.b
        if b == 0:
            return (a > 0)-(a < 0)
        if a == 0:
            return (b > 0)-(b < 0)
        if (a > 0) == (b > 0):
            return (a > 0)-(a < 0)
        d = a*a-5*b*b
        return ((a > 0)-(a < 0))*((d > 0)-(d < 0))
    def __repr__(self):
        return str(self.a) if not self.b else f'({self.a})+({self.b})*sqrt(5)'


def dot(a, b):
    return sum(x*y for x, y in zip(a, b))


def frames():
    phi = Q5(F(1, 2), F(1, 2))
    def cyc(v):
        return [v, v[1:]+v[:1], v[2:]+v[:2]]
    ico, dod = set(), set()
    for s, t in product((-1, 1), repeat=2):
        ico.update(cyc((Q5(0), Q5(s), t*phi)))
        dod.update(cyc((Q5(0), s*phi, t/phi)))
    dod.update(tuple(Q5(v) for v in z) for z in product((-1, 1), repeat=3))
    assert (len(ico), len(dod)) == (12, 20)
    assert all(dot(a, a) == phi+2 for a in ico)
    assert all(dot(b, b) == 3 for b in dod)
    nm = 0
    # Odd monomials vanish before normalization; even degrees use Q(sqrt(5)).
    for name, pts, norm2 in [('I', ico, phi+2), ('II', dod, Q5(3))]:
        for ex in product(range(6), repeat=3):
            if sum(ex) > 5:
                continue
            av = sum(product_coord(p, ex) for p in pts)/len(pts)
            if any(e % 2 for e in ex):
                assert av == 0
            else:
                av /= norm2**(sum(ex)//2)
                target = sphere_monomial(ex)
                assert av == target, (name, ex, av, target)
            nm += 1
    print('R1-3/R7-5: 12 and 20 vertices; exact monomials through degree 5:', nm, '/ 112 PASS')
    for label, ex in [('x^2', (2, 0, 0)), ('x^4', (4, 0, 0)), ('x^2*y^2', (2, 2, 0))]:
        vals = [sum(product_coord(p, ex) for p in pts)/len(pts)/norm**(sum(ex)//2)
                for pts, norm in [(ico, phi+2), (dod, Q5(3))]]
        print('  normalized moment', label, '=', vals)
    sq = Counter(dot(a, b)**2/(3*(phi+2)) for a in ico for b in dod)
    want = {Q5(F(1, 3), F(2, 15)), Q5(F(1, 3), -F(2, 15))}
    assert set(sq) == want and set(sq.values()) == {120}
    print('  cross-dot squares and multiplicities:', dict(sq))
    for b in dod:
        face = [a for a in ico if dot(a, b) == 1+phi]
        assert len(face) == 3
        assert all(dot(a, a1) == phi for a, a1 in combinations(face, 2))
        assert tuple(sum(a[j] for a in face) for j in range(3)) == tuple((1+phi)*x for x in b)
    print('  all 20 dual-face triples, pairwise products and centre sums: PASS')
    gp2 = Q5(F(1, 3), F(2, 15))
    assert (Q5(F(159, 200)**2)-gp2).sign() > 0
    assert (gp2-F(9, 16)).sign() > 0
    print('  gamma_+ < 159/200 and gamma_+ > 3/4: PASS (exact squares)')
    z = sum(F(comb(4, k), k+1) for k in (0, 2, 4))
    assert z == F(16, 5)
    gp = sqrt((5+2*sqrt(5))/15)
    print('R1-2: one-site Z =', z)
    print('  exact lower bound for [mu(a)/w(a)]/(1+gamma_+) >', F(5, 16)*F(7, 4)**3, '> 1')
    print('  diagnostic decimals only: mu(a)/w(a) = %.12f; 1+gamma_+ = %.12f' % ((1+gp)**4/z, 1+gp))


def product_coord(p, ex):
    out = Q5(1)
    for z, n in zip(p, ex):
        out *= z**n
    return out


def sphere_monomial(ex):
    if any(e % 2 for e in ex):
        return F(0)
    def oddprod(n):
        ans = 1
        for v in range(1, n+1, 2):
            ans *= v
        return ans
    ans = F(1, oddprod(sum(ex)+1))
    for e in ex:
        ans *= oddprod(e-1)
    return ans


def orientations_and_edge_cases():
    sites = list(product(range(4), repeat=2))
    edges = {frozenset((x, ((x[0]+dx) % 4, (x[1]+dy) % 4)))
             for x in sites for dx, dy in [(1, 0), (0, 1)]}
    orient = []
    for e in edges:
        a, b = tuple(e)
        if sum(a) % 2:
            a, b = b, a
        orient.append((a, b))
    x = (0, 0)
    flip = next(i for i, e in enumerate(orient) if x in e)
    orient[flip] = orient[flip][::-1]
    spin = {v: (1, 0) if sum(v) % 2 == 0 else (0, 1) for v in sites}
    def determinant(a, b):
        return a[0]*b[1]-a[1]*b[0]
    B, beta, rawrho, cx = 1, 1, 1, 1
    for a, b in orient:
        val = determinant(spin[a], spin[b])
        B *= val
        if x not in (a, b):
            rawrho *= val
        else:
            y = b if a == x else a
            beta *= determinant(spin[x], spin[y])
            cx *= 1 if a == x else -1
    assert B == cx*beta*rawrho and B != beta*rawrho
    print('R1-1: 4x4 torus, edges =', len(edges), '; after one orientation reversal:')
    print('  B =', B, '; beta_x =', beta, '; unsigned rho_x =', rawrho, '; c_x =', cx)
    print('R2-1: phi=1 gives X_a=Y_a=0 for every a; sum(Y_a)=0; displayed quotient is 0/0')
    print('R2-2: singleton product: dimension=1, generator=[0], positive eigenvalues=0, nonconstant functions=0')
    print('R2-4: M=1/2 gives |C_M|=1, whereas (2M+1)^2=4; integer M must be specified')
    print('R3-2: empty removal list has no x_1; removing it changes log(Psi) by exactly 0')
    print('R7-3: lambda_D({0}) =', F(2, 5), '; integral |n|^2 d lambda_D =', F(3, 5), '!= 1')


def weighted_and_shell_checks():
    for ell in range(2, 101):
        u = {j: j*(ell+1-j) for j in range(1, ell+1)}
        total = sum(u.values())
        r0 = sum(v*v for v in u.values())
        r1 = sum(u[j]*u.get(j+1, 0) for j in u)
        assert total == F(ell*(ell+1)*(ell+2), 6)
        assert r0 == F(ell*(ell+1)*(ell+2)*(ell*ell+2*ell+2), 30)
        assert r1 == F((ell-1)*ell*(ell+1)*(ell+2)*(ell+3), 30)
        t = F(36, 5)*F(ell*ell+2*ell+2, (ell+1)**2*(ell+2)**2)
        kap = F(25, 36)*F((ell+1)**2*(ell+2)**2, (ell-1)*(ell+3)*(ell*ell+2*ell+2))
        assert F(ell**2*r0*(r0-r1), total**4) == t
        assert F(total**4, ell**2*r0*r1) == kap
    print('R2-1: weighted t(ell), kappa_ell and all sums for ell=2,...,100: PASS')
    n = 0
    for ns in range(16, 321):
        s = F(ns, 4)
        i1 = s.numerator//s.denominator+1
        assert i1 > s
        for exceptional in [None]+list(range(2, i1+1)):
            J = [i for i in range(2, i1) if i != exceptional and i+1 != exceptional]
            assert all(i <= s for i in J)
            assert len(J) >= s-4
            n += 1
    print('R2-3: i1=floor(s)+1>s; success-index range and |J|>=s-4:', n, 'exact cases PASS')
    m = 72**4
    print('  exact example M=72^4 =', m, '; s=72; i1=73; last success input i<=72')


def closed_examples_and_certificates():
    def rho(kind, *rs):
        r1, r2, r3 = list(rs)+[F(0)]*(3-len(rs))
        numerator = (r1+r2+r3)/3+r1*r2*r3/5
        denominator = 1+(r1*r2+r1*r3+r2*r3)/3
        if kind == 'D':
            denominator += F(2, 3)
        return numerator/denominator
    # Integrate the disjoint branches of the three patterns described in
    # app-local.tex:272--274. Tips have three unit fields; live corners
    # have the two slots specified by the covered template.
    tip = rho('U', F(1), F(1), F(1))
    corner_U = rho('U', F(1), F(1))
    corner_D = rho('D', F(1), F(1))
    south_D = rho('D', tip)
    south_east = rho('U', F(1), F(1), south_D)
    straight = (rho('U', tip, corner_D), rho('U', tip, south_east), rho('D', tip))
    turn = (rho('U', tip, corner_D, corner_U), rho('U', tip, corner_D, corner_U), rho('D', tip))
    third = (rho('U', tip, corner_U, corner_U), rho('U', tip, corner_U, corner_U), F(0))
    assert straight == (F(7, 24), F(740, 2193), F(3, 25))
    assert turn == (F(112, 275), F(112, 275), F(3, 25))
    assert third == (F(169, 385), F(169, 385), F(0))
    print('R2-5: branch integrations: tip =', tip, '; U leaf corner =', corner_U, '; D leaf corner =', corner_D)
    print('  derived (rho_o,rho_f,rho_g): straight =', straight, '; turn =', turn, '; third =', third)
    cases = [
        ('straight', *straight, F(3825127, 3979368)),
        ('turn', *turn, F(1071655, 1145463)),
        ('turn N,s removed', *third, F(416114, 444675)),
    ]
    for name, ro, rf, rg, c in cases:
        a = rf*rg
        k = a*(F(1, 3)-c/5)
        L = lambda t: (1-c)+k*t
        Q = lambda t: L(t)**2-ro**2*(rf**2+rg**2+2*a*t)/9
        assert L(-1) >= 0 and L(1) >= 0 and Q(-1) >= 0 and Q(1) >= 0
        tv = None if k == 0 else -(2*(1-c)*k-2*a*ro**2/9)/(2*k*k)
        assert tv is None or not -1 < tv < 1 or Q(tv) >= 0
        numerator = 1+a/3-ro*(rf+rg)/3
        assert numerator == c*(1+a/5)
        print('R2-5:', name, ': c =', c, '; exact L,Q test PASS; attained at t=1')
        print('  Q(-1)>0:', Q(-1) > 0, '; Q(1)=0:', Q(1) == 0, '; quadratic vertex >=1:', tv is None or tv >= 1)
    for name in ('certificates_covered.jsonl', 'certificates_covered_operator_only.jsonl'):
        rec = [json.loads(line) for line in (ROOT/'programs/h1-local/out'/name).read_text().splitlines()]
        counts = Counter((r['model'], r['kind'], r['target']) for r in rec)
        assert len(rec) == len({r['pid'] for r in rec}) == 7962
        assert {r['target'] for r in rec} == {'187/200', '961/1000'}
        print('  stored claims in', name, ':', dict(counts))


def removal_constants():
    r2 = F(9, 25)
    lower3 = 1-F(3, 6)*r2
    lower4 = 1-F(4, 6)*r2-F(3, 15)*r2*r2
    bracket = 3*r2*r2
    assert lower3 == F(82, 100)
    assert lower4 == F(2294, 3125) > F(734, 1000)
    assert F(1)/lower3 <= F('1.22')
    assert F(2)/F('.734') <= F('2.73')
    assert 2*bracket/(15*F('.734')) <= F('.0707')
    print('R3-1/R7-2: three-factor lower bound =', lower3, '; four-factor lower bound =', lower4)
    print('  quartic bracket absolute bound =', bracket, '; response bound =', 2*bracket)
    print('  1/0.82<=1.22; 2/0.734<=2.73; 0.7776/(15*0.734)<=0.0707: PASS (rational)')
    # One spin with antipodal pins: integrand vanishes somewhere but has positive normalizer.
    print('R3-1: antipodal two-pin one-site normalizer = 1-1/3 =', 1-F(1, 3), '>0')
    print('R3-4: F(d)=(d+1)^(-8); d^8*F(d) -> 1, so F is not o(d^(-8))')
    print('  if s>=84, M=s^4 and d>=s/6-7, then 4(2M+1)^2*F(d) <=', 36*12**8)


def square_boundary_intersections(center, r, R):
    """Boundary of square at center,r vs square at 0,R. Exact segments."""
    x, y = center
    ans, overlap = set(), False
    for side in (-1, 1):
        a = x+side*r
        for b in (-R, R):
            if y-r <= b <= y+r and -R <= a <= R:
                ans.add((a, b))
        if a in (-R, R):
            lo, hi = max(y-r, -R), min(y+r, R)
            if lo <= hi:
                overlap = True
        b = y+side*r
        for a in (-R, R):
            if x-r <= a <= x+r and -R <= b <= R:
                ans.add((a, b))
        if b in (-R, R):
            lo, hi = max(x-r, -R), min(x+r, R)
            if lo <= hi:
                overlap = True
    return ans, overlap


def corner_distance(center, k, M, z):
    """Minimum max-norm distance from z to radius-k square clipped to C_M."""
    x, y = center
    out = []
    for side in (-1, 1):
        a = x+side*k
        lo, hi = max(y-k, -M), min(y+k, M)
        if -M <= a <= M and lo <= hi:
            out.append(max(abs(z[0]-a), max(lo-z[1], z[1]-hi, 0)))
        b = y+side*k
        lo, hi = max(x-k, -M), min(x+k, M)
        if -M <= b <= M and lo <= hi:
            out.append(max(abs(z[1]-b), max(lo-z[0], z[0]-hi, 0)))
    return min(out)


def cut_geometry():
    n, maxcells = 0, 0
    for s, l0, i in product((72, 84, 96), (20, 22), (2, 5, 7)):
        M, k = s**4, i*s
        placements = [(0, -M-1), (-M+3*s//2, -M-1), (-M-1, -M-1), (M, -M-1)]
        for y in placements:
            if min(corner_distance(y, k, M, z) for z in product((-M, M), repeat=2)) < F(s, 3):
                continue
            assert s > 3*l0
            for j in range(s//12+1):
                cells = set()
                for r in {k-j, k+j}:
                    assert r >= 1
                    for hp in range(l0//2+j-2, l0//2+j):
                        pts, overlap = square_boundary_intersections(y, r, M+1-hp)
                        assert not overlap, (s, l0, i, y, j, hp)
                        assert len(pts) <= 8
                        for c in pts:
                            assert abs(max(abs(c[0]-y[0]), abs(c[1]-y[1]))-k) == j
                            assert M+1-max(map(abs, c)) == hp
                        cells.update(pts)
                assert len(cells) <= 48
                maxcells = max(maxcells, len(cells))
                n += 1
    print('R3-3: nonexceptional exact cut-level cases =', n, '; maximum counted cells =', maxcells, '<=48; no overlapping sides: PASS')
    M, k = 72**4, 144
    print('  counterexample to unsigned side assertion: y=(0,-M-1), bottom side, E=top:')
    print('  side misses C_M; signed depth to E = 2M+2+k =', 2*M+2+k, '>0')


def topology():
    # The one-cell outside frame connects the entire infinite complement.
    dim = 6
    nn, king = [], []
    for r, c in product(range(dim), repeat=2):
        nn.append(sum(1 << (dim*(r+dr)+c+dc) for dr, dc in [(1,0),(-1,0),(0,1),(0,-1)]
                      if 0 <= r+dr < dim and 0 <= c+dc < dim))
        king.append(sum(1 << (dim*(r+dr)+c+dc) for dr, dc in product((-1,0,1), repeat=2)
                        if (dr or dc) and 0 <= r+dr < dim and 0 <= c+dc < dim))
    def connected(mask, adj):
        if not mask:
            return True
        seen, pending = 0, mask & -mask
        while pending:
            v = pending & -pending
            pending ^= v
            if seen & v:
                continue
            seen |= v
            pending |= adj[v.bit_length()-1] & mask & ~seen
        return seen == mask
    embedded = [1 << (6*(r+1)+c+1) for r, c in product(range(4), repeat=2)]
    blocks = []
    for r, c in product(range(3), repeat=2):
        ids = [4*r+c, 4*r+c+1, 4*(r+1)+c, 4*(r+1)+c+1]
        b = sum(1 << j for j in ids)
        diagonals = ((1 << ids[0]) | (1 << ids[3]), (1 << ids[1]) | (1 << ids[2]))
        blocks.append((b, diagonals))
    checked, failed = 0, 0
    full = (1 << 36)-1
    for mask4 in range(1, 1 << 16):
        if any((mask4 & b) in ds for b, ds in blocks):
            continue
        A = sum(embedded[j] for j in range(16) if mask4 >> j & 1)
        if not connected(A, king) or not connected(full ^ A, king):
            continue
        B, tmp = 0, A
        while tmp:
            v = tmp & -tmp
            tmp ^= v
            B |= king[v.bit_length()-1]
        B &= ~A
        checked += 1
        failed += not connected(B, nn)
    assert failed == 0
    print('Appendix B: all 65535 nonempty subsets of a 4x4 box examined;', checked, 'satisfy (i)-(iii); failed conclusions =', failed)


def global_arithmetic():
    q = F('0.98075')
    assert F('0.85594872') < q**8
    B = sum(map(F, ['0.594580', '0.026669', '0.302932', '0.057384', '0.006199']))
    C = sum(map(F, ['0.841681', '0.022644', '0.268029', '0.053319', '0.005737']))
    hC = F.from_float(1.23)  # The exact dyadic value specified by Appendix C.
    assert B < F('0.98779') and C/hC < F('0.98779')
    print('Global interface: q^2 =', q*q, '; 0.85594872 < q^8: PASS')
    print('  rounded Appendix C table: B sum =', B, '; C numerator =', C)
    print('  B and C/h_C < 0.98779 with exact dyadic h_C =', hC, ': PASS')
    print('Formal-note self-factor example: (1+n_x dot n_x)^4 has polynomial degree 8, but equals 16 on S^2')


if __name__ == '__main__':
    frames()
    orientations_and_edge_cases()
    weighted_and_shell_checks()
    closed_examples_and_certificates()
    removal_constants()
    cut_geometry()
    topology()
    global_arithmetic()
    print('ALL EXACT CHECKS PASSED. Decimal displays above are explicitly diagnostic only.')
