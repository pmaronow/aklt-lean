"""Exact (rational) certificate for fully decoupled patterns (agent 70, NOTES Prop. 1.4 / Entry 6).

After the tree collapse the three v-neighbours are independent with means of norm rho_o, rho_f, rho_g (rationals), and
inf Z_cur/Z_next >= c  <=>  for all t in [-1,1]:  L(t) := (1-c) + a t (1/3 - c/5) >= (rho_o/3) sqrt(rho_f^2+rho_g^2+2 a t),
a = rho_f rho_g  <=>  L >= 0 on [-1,1] (linear: endpoints) and
Q(t) := L(t)^2 - (rho_o^2/9)(rho_f^2 + rho_g^2 + 2 a t) >= 0 on [-1,1] (quadratic: endpoints and vertex).  All in Fractions."""
import sys, collections
from fractions import Fraction as Fr
sys.path.insert(0, '/home/user/otis-claude/research/aklt-gap/agents/70-local-bounds/code')
from ring import Pattern, load, RING, TIP, bk, C0, C1, C2, C3, TIPRAD

CORN = (C0, C1, C2, C3)


def rho_exact(kind, rs):
    rs = list(rs) + [Fr(0)] * (3 - len(rs))
    assert len(rs) == 3
    r1, r2, r3 = rs
    num = (r1 + r2 + r3) / 3 + r1 * r2 * r3 / 5
    den = 1 + (r1 * r2 + r1 * r3 + r2 * r3) / 3
    if kind == 'd':
        den += Fr(2, 3)
    return num / den


def radii_exact(p):
    """prune pendant trees; returns (decoupled?, {v-neighbour: rho}) with exact rationals."""
    adj = collections.defaultdict(set)
    for i in range(8):
        if p.ringbond[i]:
            a, b = RING[i], RING[(i + 1) % 8]
            adj[a].add(b); adj[b].add(a)
    alive = set(x for x in RING if p.live[x] or x in p.vn)
    seen = set()
    for x in p.vn:
        st = [x]; seen.add(x)
        while st:
            y = st.pop()
            for z in adj[y]:
                if z in alive and z not in seen:
                    seen.add(z); st.append(z)
    alive &= seen
    fields = {}
    for x in alive:
        f = []
        if x in TIP and bk(x, TIP[x]) in p.present:
            f.append(TIPRAD)
        if x in CORN:
            f += [Fr(1)] * p.nslot[x]
        fields[x] = f
    changed = True
    while changed:
        changed = False
        for x in list(alive):
            if x in p.vn:
                continue
            nb = adj[x] & alive
            if len(nb) <= 1:
                alive.discard(x); changed = True
                if len(nb) == 1:
                    y = next(iter(nb))
                    r = rho_exact(p.kind[x], fields[x])
                    if r > 0:
                        fields[y].append(r)
    edges = any(adj[x] & alive for x in alive)
    if edges:
        return False, None
    return True, {x: rho_exact(p.kind[x], fields[x]) for x in p.vn}


def certify_decoupled(p, c):
    """c a Fraction.  Returns (applicable, certified, radii)."""
    dec, rad = radii_exact(p)
    if not dec:
        return False, False, None
    ro = rad[p.out]
    fg = p.fg
    rf = rad[fg[0]] if len(fg) > 0 else Fr(0)
    rg = rad[fg[1]] if len(fg) > 1 else Fr(0)
    a = rf * rg
    k = a * (Fr(1, 3) - c / 5)
    L = lambda t: (1 - c) + k * t
    if L(Fr(-1)) < 0 or L(Fr(1)) < 0:
        return True, False, rad
    # Q(t) = (1-c)^2 + 2(1-c)k t + k^2 t^2 - (ro^2/9)(rf^2+rg^2) - (2 a ro^2/9) t
    q2 = k * k
    q1 = 2 * (1 - c) * k - 2 * a * ro * ro / 9
    q0 = (1 - c) ** 2 - ro * ro * (rf * rf + rg * rg) / 9
    Q = lambda t: q0 + q1 * t + q2 * t * t
    ok = Q(Fr(-1)) >= 0 and Q(Fr(1)) >= 0
    if ok and q2 > 0:
        tv = -q1 / (2 * q2)
        if -1 < tv < 1 and Q(tv) < 0:
            ok = False
    return True, ok, rad


if __name__ == '__main__':
    # usage: closed_exact.py [ps/qs pt/qt]   (default 961/1000 187/200); tip radius from TIPRAD
    cs = Fr(sys.argv[1]) if len(sys.argv) > 1 else Fr(961, 1000)
    ct = Fr(sys.argv[2]) if len(sys.argv) > 2 else Fr(187, 200)
    P = load()
    for refined in (False, True):
        n = 0; nok = 0; fails = []
        for r in P:
            p = Pattern(r, refined=refined)
            c = cs if p.out == (0, 1) else ct
            app, ok, rad = certify_decoupled(p, c)
            if app:
                n += 1; nok += ok
                if not ok:
                    fails.append(r['pid'])
        print('tip radius', TIPRAD, '| refined' if refined else '| covered (agent 57 model)', ': decoupled patterns', n,
              'certified exactly at (%s, %s):' % (cs, ct), nok, 'fails', fails)
