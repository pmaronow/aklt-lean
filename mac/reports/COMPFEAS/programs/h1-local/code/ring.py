"""Exact float engine for the level-1 patch in ring form (agent 70).

After integrating v, Z_cur = Z_w + (C_eN + C_eW + C_NW)/3 and Z_next = Z_w + C_fg/5, where Z_w, C_xy are the partition
function and the unnormalised pair correlations <n_x.n_y> of the patch measure w with v removed (agent 63 Lemma 63.2):
the ring e - c0 - N - c1 - W - c2 - s - c3 - e (c0=(1,1), c1=(-1,1), c2=(-1,-1), c3=(1,-1)) with pendant tips
(field mu = (3/5)u on the d1 site, exact leaf reduction) and two slots on every live corner.
Spin integrals are done exactly with the 12 vertices of the icosahedron (a spherical 5-design; every site integrand has
degree <= 4) plus the zero vector for the delta_0 part of diluted sites.
Pattern format: agent 57/63 P_ext (kinds of live sites, present bonds, out)."""
import ast, json
import numpy as np

V = (0, 0)
E, N, W, S = (1, 0), (0, 1), (-1, 0), (0, -1)
C0, C1, C2, C3 = (1, 1), (-1, 1), (-1, -1), (1, -1)
RING = [E, C0, N, C1, W, C2, S, C3]
TIP = {E: (2, 0), N: (0, 2), W: (-2, 0), S: (0, -2)}
P63 = '/home/user/otis-claude/research/aklt-gap/agents/63-certify-N/out/pext7962.json'
import os
from fractions import Fraction as _Fr
# radius of the field of a tip on its d1 site: 3/5 (level 1: three unit slots) or 37/65 (level 1+: the far tip
# (3,0) is added to the patch as a pendant site, NOTES 6.3).  Set by the environment variable TIPRAD = "a/b".
TIPRAD = _Fr(os.environ.get('TIPRAD', '3/5'))


def ico():
    g = (1 + 5 ** 0.5) / 2
    p = []
    for a in (-1, 1):
        for b in (-g, g):
            p += [(0, a, b), (a, b, 0), (b, 0, a)]
    p = np.array(p, float)
    return p / np.linalg.norm(p, axis=1, keepdims=True)


FR = np.vstack([ico(), np.zeros((1, 3))])          # 13 states: 12 frame points + zero vector
GR = FR @ FR.T                                     # Gram of states
BOND = 1.0 + GR                                    # (1 + n.n')
ONES = np.ones((13, 13))


def bk(a, b):
    return frozenset((tuple(a), tuple(b)))


class Pattern:
    def __init__(self, r, refined=False):
        self.r = r
        self.refined = refined
        self.out = tuple(r['out'])
        self.kind = {ast.literal_eval(k): c for k, c in r['kinds'].items()}
        self.present = set(bk(a, b) for a, b in r['present'])
        self.vn = [x for x in (E, N, W) if bk(V, x) in self.present]
        assert self.out in self.vn
        self.fg = [x for x in self.vn if x != self.out]
        self.live = {x: any(x in b for b in self.present) for x in RING}
        for x in RING:
            if self.live[x]:
                assert x in self.kind, (x, r)
        # variables: list of (site, type) ; type 'tip' (radius 3/5 field on a d1 site) or 'slot' (unit field on a corner)
        self.vars = []
        for x in (E, N, W, S):
            if bk(x, TIP[x]) in self.present:
                self.vars.append((x, 'tip'))
        self.nslot = {}
        for i, c in ((1, C0), (3, C1), (5, C2), (7, C3)):
            k = int(bk(RING[i - 1], c) in self.present) + int(bk(c, RING[(i + 1) % 8]) in self.present)
            ns = 0
            if self.live[c]:
                ns = 2 - k if (refined and self.kind[c] == 'd') else 2
            self.nslot[c] = ns
            for _ in range(ns):
                self.vars.append((c, 'slot'))
        self.nv = len(self.vars)
        self.rad = np.array([float(TIPRAD) if t == 'tip' else 1.0 for _, t in self.vars])
        self.ringbond = [bk(RING[i], RING[(i + 1) % 8]) in self.present for i in range(8)]

    def base(self, x):
        """measure weights over the 13 states"""
        if not self.live[x] and x not in self.vn:
            w = np.zeros(13); w[12] = 1.0
            return w
        k = self.kind.get(x, 'u')
        w = np.zeros(13)
        if k == 'u':
            w[:12] = 1 / 12
        else:
            w[:12] = 0.6 / 12; w[12] = 0.4
        return w

    def site_weights(self, U):
        """U: (nv,3) unit vectors. returns dict site -> weight vector (13)"""
        om = {x: self.base(x) for x in RING}
        for (x, t), r, u in zip(self.vars, self.rad, U):
            om[x] = om[x] * (1.0 + r * (FR @ u))
        return om

    def moments(self, U):
        """returns Z, C_eN, C_eW, C_NW (unnormalised; C_xy = 0 unless both are v-neighbours)"""
        om = self.site_weights(U)
        B = [BOND if p else ONES for p in self.ringbond]     # B[i]: bond RING[i]-RING[i+1]
        XeN = (B[0] * om[C0][None, :]) @ B[1]
        XNW = (B[2] * om[C1][None, :]) @ B[3]
        XWe = (B[4] * om[C2][None, :]) @ (B[5] * om[S][None, :]) @ (B[6] * om[C3][None, :]) @ B[7]
        Em = om[E][:, None, None] * om[N][None, :, None] * om[W][None, None, :] \
            * XeN[:, :, None] * XNW[None, :, :] * XWe.T[:, None, :]
        Z = Em.sum()
        pe, pn, pw = (E in self.vn), (N in self.vn), (W in self.vn)
        CeN = (Em.sum(2) * GR).sum() if (pe and pn) else 0.0
        CeW = (Em.sum(1) * GR).sum() if (pe and pw) else 0.0
        CNW = (Em.sum(0) * GR).sum() if (pn and pw) else 0.0
        return Z, CeN, CeW, CNW

    def cur_next(self, U):
        Z, CeN, CeW, CNW = self.moments(U)
        cur = Z + (CeN + CeW + CNW) / 3
        if len(self.fg) == 2:
            f, g = self.fg
            cfg = {frozenset((E, N)): CeN, frozenset((E, W)): CeW, frozenset((N, W)): CNW}[frozenset((f, g))]
        else:
            cfg = 0.0
        return cur, Z + cfg / 5

    def ratio(self, U):
        a, b = self.cur_next(U)
        return a / b

    def lf_coeffs(self, U, i):
        """ratio as a function of u_i (others fixed): (a0 + a.u)/(b0 + b.u)"""
        U = U.copy()
        U[i] = 0
        a0, b0 = self.cur_next(U)
        a = np.zeros(3); b = np.zeros(3)
        for k in range(3):
            U[i] = 0; U[i, k] = 1
            ak, bk_ = self.cur_next(U)
            a[k] = ak - a0; b[k] = bk_ - b0
        return a0, a, b0, b

    def minimise(self, restarts=4, seed=0, sweeps=400, tol=1e-13, U0=None):
        rng = np.random.default_rng(seed)
        best = (9.0, None)
        if self.nv == 0:
            return self.ratio(np.zeros((0, 3))), np.zeros((0, 3))
        for t in range(restarts):
            if U0 is not None and t == 0:
                U = U0.copy()
            else:
                U = rng.normal(size=(self.nv, 3)); U /= np.linalg.norm(U, axis=1, keepdims=True)
            val = self.ratio(U)
            for sw in range(sweeps):
                old = val
                for i in rng.permutation(self.nv):
                    a0, a, b0, b = self.lf_coeffs(U, i)
                    # min over unit u of (a0+a.u)/(b0+b.u): smaller root l of |a - l b|^2 = (a0 - l b0)^2
                    A = b0 * b0 - b @ b; Bq = a0 * b0 - a @ b; Cq = a0 * a0 - a @ a
                    l = (Bq - np.sqrt(max(Bq * Bq - A * Cq, 0.0))) / A
                    d = a - l * b
                    nd = np.linalg.norm(d)
                    if nd > 1e-14:
                        U[i] = -d / nd
                    val = l
                if old - val < tol:
                    break
            if val < best[0]:
                best = (val, U.copy())
        return best


def load():
    return json.load(open(P63))


if __name__ == '__main__':
    import sys, time
    P = load()
    ids = [int(x) for x in sys.argv[1:]] or [7645, 1382, 5287, 5441, 1383, 7863]
    for pid in ids:
        p = Pattern(P[pid])
        t = time.time()
        val, U = p.minimise(restarts=3, seed=1)
        print(pid, 'out', p.out, 'nv', p.nv, 'min57', P[pid]['min57'], 'mine', round(val, 9), 'time', round(time.time() - t, 1))
