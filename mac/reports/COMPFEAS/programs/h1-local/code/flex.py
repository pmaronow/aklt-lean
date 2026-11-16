"""Flexible experiments on top of ring.py (agent 70): extra fixed fields, s-cut by the xi-mixture, tied slots.

s-cut (NOTES Entry 3): if s is diluted, keeps exactly its two corner bonds and has no tip, its kernel is
1 + n_c3.n_c2/5 = E_xi[(1 + al xi.n_c3)(1 + al xi.n_c2)], al = sqrt(3/5), xi uniform on the sphere.  So
Z_cur/Z_next >= inf_xi of the ratio of the pattern with s removed and the extra field al*xi on c3 and on c2
(bound B: shared xi, fixed to e_z by rotation; bound A: independent unit vectors on c3 and c2)."""
import sys
import numpy as np
from scipy.optimize import minimize
sys.path.insert(0, '/home/user/otis-claude/research/aklt-gap/agents/70-local-bounds/code')
from ring import Pattern, load, FR, RING, E, N, W, S, C0, C1, C2, C3, bk, TIP

AL = (3 / 5) ** 0.5


class Flex(Pattern):
    def __init__(self, r, refined=True, scut=None, tie=()):
        """scut: None | 'A' | 'B'.  tie: corners whose two slots are tied (m1 = m2)."""
        Pattern.__init__(self, r, refined=refined)
        self.fixed = []            # list of (site, vector)
        self.scut = scut
        if scut:
            assert self.has_slink()
            # remove s: drop its two ring bonds
            i = RING.index(S)
            self.ringbond[i - 1] = False; self.ringbond[i] = False
            self.live[S] = False
            if scut == 'A':
                self.vars.append((C3, 'xi')); self.vars.append((C2, 'xi'))
                self.rad = np.append(self.rad, [AL, AL])
            else:
                self.fixed += [(C3, AL * np.array([0, 0, 1.0])), (C2, AL * np.array([0, 0, 1.0]))]
            self.nv = len(self.vars)
        self.tie = tuple(tie)

    def has_slink(self):
        i = RING.index(S)
        return (self.live[S] and self.kind[S] == 'd' and self.ringbond[i - 1] and self.ringbond[i]
                and bk(S, TIP[S]) not in self.present)

    def site_weights(self, U):
        om = Pattern.site_weights(self, U)
        for x, f in self.fixed:
            om[x] = om[x] * (1.0 + FR @ f)
        return om

    def expand(self, Y):
        """free parameters (unit vectors) -> full U with ties applied"""
        U = Y.copy()
        for c in self.tie:
            idx = [i for i, (x, t) in enumerate(self.vars) if x == c and t == 'slot']
            if len(idx) == 2:
                U[idx[1]] = U[idx[0]]
        return U

    def minimise_generic(self, restarts=6, seed=0, Y0=None):
        rng = np.random.default_rng(seed)
        best = (9.0, None)

        def f(y):
            Y = y.reshape(-1, 3)
            Y = Y / np.linalg.norm(Y, axis=1, keepdims=True)
            return self.ratio(self.expand(Y))
        for t in range(restarts):
            y0 = Y0.ravel() if (Y0 is not None and t == 0) else rng.normal(size=3 * self.nv)
            r = minimize(f, y0, method='L-BFGS-B', options={'maxiter': 2000, 'ftol': 1e-15, 'gtol': 1e-10})
            if r.fun < best[0]:
                Y = r.x.reshape(-1, 3)
                best = (r.fun, self.expand(Y / np.linalg.norm(Y, axis=1, keepdims=True)))
        return best


if __name__ == '__main__':
    P = load()
    ids = [int(a) for a in sys.argv[1:]] or [5287, 5441, 7863, 3596, 5420, 7697]
    for pid in ids:
        base = Flex(P[pid], refined=True)
        v0, U0 = base.minimise(restarts=3, seed=1)
        line = 'pid %d out %s nv %d refined-exact %.6f (57 covered %.6f)' % (pid, base.out, base.nv, v0, P[pid]['min57'])
        if base.has_slink():
            a = Flex(P[pid], refined=True, scut='A'); va, _ = a.minimise(restarts=3, seed=2)
            b = Flex(P[pid], refined=True, scut='B'); vb, _ = b.minimise(restarts=6, seed=3)
            line += '  s-cut A %.6f  B %.6f' % (va, vb)
        print(line, flush=True)
