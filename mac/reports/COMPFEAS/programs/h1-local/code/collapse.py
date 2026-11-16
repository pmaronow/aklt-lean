"""Tree collapse (agent 70, NOTES Entry 1): pendant-tree radii and the closed-form value of fully decoupled patterns.

rho(kind; r_1..r_k) = sup |mean of n| under  lambda_kind(dn) prod_j (1 + beta_j.n), |beta_j| <= r_j  (Lemma 1.2):
   uniform:  ((r1+r2+r3)/3 + r1 r2 r3/5) / (1 + (r1 r2 + r1 r3 + r2 r3)/3)
   diluted:  same numerator / (same denominator + 2/3).
A pendant tree attached to y through the bond (t0, y) acts on y through a field in the ball of radius
rho(kind(t0); radii of t0's own slots (1 each) and of its child subtrees).
Fully decoupled pattern (no surviving bond between v-neighbours after pruning):
   R = min_{t in [-1,1]} (1 + a t/3 - (rho_o/3) sqrt(rho_f^2 + rho_g^2 + 2 a t)) / (1 + a t/5),  a = rho_f rho_g."""
import sys, json, collections
import numpy as np
sys.path.insert(0, '/home/user/otis-claude/research/aklt-gap/agents/70-local-bounds/code')
from ring import Pattern, load, RING, TIP, E, N, W, S, V, bk, C0, C1, C2, C3

CORN = (C0, C1, C2, C3)


def rho(kind, rs):
    rs = list(rs) + [0.0] * (3 - len(rs))
    assert len(rs) == 3
    r1, r2, r3 = rs
    num = (r1 + r2 + r3) / 3 + r1 * r2 * r3 / 5
    den = 1 + (r1 * r2 + r1 * r3 + r2 * r3) / 3
    if kind == 'd':
        den += 2.0 / 3
    return num / den


class Tree:
    """graph H of a pattern (ring sites; tips are folded in as fields of radius 3/5)."""

    def __init__(self, p):
        self.p = p
        self.adj = collections.defaultdict(set)
        for i in range(8):
            if p.ringbond[i]:
                a, b = RING[i], RING[(i + 1) % 8]
                self.adj[a].add(b); self.adj[b].add(a)
        self.own = {}
        for x in RING:
            f = []
            if x in TIP and bk(x, TIP[x]) in p.present:
                f.append(0.6)
            if x in CORN and p.live[x]:
                f += [1.0] * p.nslot[x]
            self.own[x] = f
        self.vn = list(p.vn)
        self.prune()

    def prune(self):
        alive = set(x for x in RING if self.p.live[x] or x in self.vn)
        # only components containing a v-neighbour matter; others drop out (their factors cancel)
        seen = set()
        for x in self.vn:
            st = [x]; seen.add(x)
            while st:
                y = st.pop()
                for z in self.adj[y]:
                    if z in alive and z not in seen:
                        seen.add(z); st.append(z)
        alive &= seen
        fields = {x: list(self.own[x]) for x in alive}
        changed = True
        while changed:
            changed = False
            for x in list(alive):
                if x in self.vn:
                    continue
                nb = self.adj[x] & alive
                if len(nb) <= 1:
                    alive.discard(x); changed = True
                    if len(nb) == 1:
                        y = next(iter(nb))
                        r = rho(self.p.kind[x], fields[x])
                        if r > 0:
                            fields[y].append(r)
        self.alive = alive
        self.fields = {x: fields[x] for x in alive}
        self.edges = set(frozenset((x, y)) for x in alive for y in self.adj[x] & alive)

    def decoupled(self):
        return len(self.edges) == 0

    def radii(self):
        return {x: rho(self.p.kind[x], self.fields[x]) for x in self.vn}


def gram_min(ro, rf, rg, has_fg=True, ngrid=20001):
    """min over unit vectors of (1 + (ro rf g_of + ro rg g_og + rf rg g_fg)/3)/(1 + rf rg g_fg/5) (float, grid+refine)."""
    a = rf * rg
    t = np.linspace(-1, 1, ngrid)
    val = (1 + a * t / 3 - (ro / 3) * np.sqrt(np.maximum(rf * rf + rg * rg + 2 * a * t, 0))) / (1 + a * t / 5)
    i = int(np.argmin(val))
    lo, hi = t[max(i - 1, 0)], t[min(i + 1, ngrid - 1)]
    tt = np.linspace(lo, hi, 2001)
    v2 = (1 + a * tt / 3 - (ro / 3) * np.sqrt(np.maximum(rf * rf + rg * rg + 2 * a * tt, 0))) / (1 + a * tt / 5)
    j = int(np.argmin(v2))
    return float(v2[j]), float(tt[j])


def decoupled_value(p, tr=None):
    tr = tr or Tree(p)
    rad = tr.radii()
    ro = rad[p.out]
    fg = p.fg
    rf = rad[fg[0]] if len(fg) > 0 else 0.0
    rg = rad[fg[1]] if len(fg) > 1 else 0.0
    return gram_min(ro, rf, rg)[0], rad


if __name__ == '__main__':
    P = load()
    refined = len(sys.argv) > 1 and sys.argv[1] == 'refined'
    nd = 0; worst = 0.0; rows = []
    for r in P:
        p = Pattern(r, refined=refined)
        tr = Tree(p)
        if not tr.decoupled():
            continue
        nd += 1
        val, rad = decoupled_value(p, tr)
        d = val - r['min57']
        rows.append((r['pid'], val, r['min57'], d))
        if abs(d) > abs(worst):
            worst = d
    print('fully decoupled patterns:', nd)
    print('max |closed form - min57|:', worst)
    rows.sort(key=lambda x: x[3])
    print('most negative differences (closed form below min57):', rows[:5])
    print('most positive:', rows[-5:])
    for typ, out in (('S', (0, 1)), ('T', (1, 0))):
        sel = sorted((x[1], x[0]) for x in rows if tuple(P[x[0]]['out']) == out)
        print(typ, 'count', len(sel), 'lowest closed-form values', sel[:6])
