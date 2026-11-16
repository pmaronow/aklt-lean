"""Memory-m over-count of the closed-trail MASS u -> v (measurement, floating point).
   Exact trails for the first m steps (DFS), then memory-m walks (bond memory m; revisit seen in the window -> 1/5,
   else x_type/3), c avoided, v absorbing.  Prints the closed mass per length n.
   Usage: python3 memdp.py X m Nmax cs ct"""
import sys
import numpy as np
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from memgrowth import windows, transitions, code

DX = [1, 0, -1, 0]; DY = [0, 1, 0, -1]


def exact_prefix(X, m, xs, xt):
    u = (-1, 0); v = (1, 0) if X == 'B' else (0, 1); c = (0, 0)
    closed = {}
    pref = {}  # (dirs tuple, endpoint) -> weight
    path = [u]; dirs = []; used = set()

    def weight(n):
        w = 1.0
        for j in range(n):
            if path[j] in path[:j]:
                w *= 0.2; continue
            ain = 2 if j == 0 else dirs[j - 1]
            w *= xs / 3 if dirs[j] == ain else xt / 3
        return w

    def dfs(n):
        p = path[-1]
        if n > 0 and p == v:
            closed[n] = closed.get(n, 0) + weight(n); return
        if n == m:
            key = (tuple(dirs), p); pref[key] = pref.get(key, 0) + weight(n); return
        for d in range(4):
            q = (p[0] + DX[d], p[1] + DY[d])
            if q == c: continue
            b = (min(p, q), max(p, q))
            if b in used: continue
            used.add(b); path.append(q); dirs.append(d)
            dfs(n + 1)
            used.discard(b); path.pop(); dirs.pop()
    dfs(0)
    return closed, pref, u, v, c


def main():
    X = sys.argv[1]; m = int(sys.argv[2]); Nmax = int(sys.argv[3]); cs, ct = float(sys.argv[4]), float(sys.argv[5])
    xs, xt = 1 / min(cs, 1), 1 / min(ct, 1)
    closed, pref, u, v, c = exact_prefix(X, m, xs, xt)
    seqs = windows(m); tgt, kind = transitions(seqs)
    codes = code(seqs); idx = {int(k): i for i, k in enumerate(codes)}
    R = Nmax // 2 + 3; S = 2 * R + 1
    V = np.zeros((len(seqs), S, S))
    for (ds, p), w in pref.items():
        k = int(sum(d * 4 ** (m - 1 - i) for i, d in enumerate(ds)))
        V[idx[k], p[0] + R, p[1] + R] += w
    W = np.array([xs / 3, xt / 3, 0.2])[kind]
    out = dict(closed)
    for t in range(m, Nmax):
        new = np.zeros_like(V)
        for d in range(4):
            ok = np.nonzero(tgt[:, d] >= 0)[0]
            T = tgt[ok, d]; order = np.argsort(T, kind='stable'); ok = ok[order]; T = T[order]
            contrib = V[ok] * W[ok, d][:, None, None]
            starts = np.r_[0, np.nonzero(np.diff(T))[0] + 1]
            summed = np.add.reduceat(contrib, starts, axis=0)
            tg = T[starts]
            sx, sy = DX[d], DY[d]
            # shift positions by (sx, sy)
            src = summed[:, max(0, -sx):S - max(0, sx), max(0, -sy):S - max(0, sy)]
            new[tg, max(0, sx):S - max(0, -sx), max(0, sy):S - max(0, -sy)] += src
        new[:, c[0] + R, c[1] + R] = 0
        arr = new[:, v[0] + R, v[1] + R].sum()
        out[t + 1] = out.get(t + 1, 0) + arr
        new[:, v[0] + R, v[1] + R] = 0
        # truncate positions that cannot return in time
        V = new
        rem = Nmax - (t + 1)
        xs_ = np.arange(S) - R
        dist = np.abs(xs_[:, None] - v[0]) + np.abs(xs_[None, :] - v[1])
        V[:, dist > rem] = 0
        print(t + 1, f"{out[t + 1]:.6e}", flush=True)
    return out


if __name__ == '__main__':
    main()
