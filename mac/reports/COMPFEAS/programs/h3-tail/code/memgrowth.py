"""Growth rate (spectral radius at k = 0) of memory-m bond walks on Z^2 with passage weights
   first visit (as seen by the window): straight xs/3, turn xt/3;  revisit (current site among the window sites): 1/5;
   forbidden: reuse of one of the last m bonds.  States: the last m step directions (non-reversing, and the window
   itself a trail).  Usage: python3 memgrowth.py cs ct m1 m2"""
import sys
import numpy as np

DX = np.array([1, 0, -1, 0]); DY = np.array([0, 1, 0, -1])


def windows(m):
    """all non-reversing direction sequences of length m that are trails; returns array (N, m) int8"""
    seqs = np.array([[d] for d in range(4)], dtype=np.int8)
    for _ in range(m - 1):
        new = []
        for d in range(4):
            ok = seqs[:, -1] != (d + 2) % 4
            s = seqs[ok]
            new.append(np.hstack([s, np.full((len(s), 1), d, np.int8)]))
        seqs = np.vstack(new)
        seqs = seqs[is_trail(seqs)]
    return seqs


def positions(seqs):
    x = np.zeros((len(seqs), seqs.shape[1] + 1), np.int32); y = x.copy()
    x[:, 1:] = np.cumsum(DX[seqs], axis=1); y[:, 1:] = np.cumsum(DY[seqs], axis=1)
    return x, y


def is_trail(seqs):
    x, y = positions(seqs)
    L = seqs.shape[1]
    # bond keys: unordered pair of endpoints
    ax, ay, bx, by = x[:, :-1], y[:, :-1], x[:, 1:], y[:, 1:]
    swap = (ax > bx) | ((ax == bx) & (ay > by))
    k1x = np.where(swap, bx, ax); k1y = np.where(swap, by, ay); k2x = np.where(swap, ax, bx); k2y = np.where(swap, ay, by)
    key = ((k1x + 64) * 128 + (k1y + 64)) * 2 + (k2x != k1x)
    ks = np.sort(key, axis=1)
    return ~np.any(ks[:, 1:] == ks[:, :-1], axis=1)


def code(seqs):
    m = seqs.shape[1]
    return (seqs.astype(np.int64) * (4 ** np.arange(m - 1, -1, -1))).sum(1)


def transitions(seqs):
    """for each state and each new direction d: (target index or -1, kind 0 straight /1 turn /2 revisit)"""
    N, m = seqs.shape
    x, y = positions(seqs)
    cx, cy = x[:, -1], y[:, -1]
    rev = np.zeros(N, bool)
    for i in range(m):
        rev |= (x[:, i] == cx) & (y[:, i] == cy)
    codes = code(seqs); order = np.argsort(codes); sc = codes[order]
    tgt = -np.ones((N, 4), np.int64); kind = np.zeros((N, 4), np.int8)
    for d in range(4):
        nx, ny = cx + DX[d], cy + DY[d]
        bad = seqs[:, -1] == (d + 2) % 4
        for i in range(m):  # bond (p_i, p_{i+1}) equals {c, n}?
            bad |= (x[:, i] == cx) & (y[:, i] == cy) & (x[:, i + 1] == nx) & (y[:, i + 1] == ny)
            bad |= (x[:, i + 1] == cx) & (y[:, i + 1] == cy) & (x[:, i] == nx) & (y[:, i] == ny)
        newc = (codes % (4 ** (m - 1))) * 4 + d
        pos = np.searchsorted(sc, newc); pos = np.minimum(pos, N - 1)
        found = sc[pos] == newc
        t = np.where(found & ~bad, order[pos], -1)
        tgt[:, d] = t
        kind[:, d] = np.where(rev, 2, np.where(seqs[:, -1] == d, 0, 1))
    return tgt, kind


def growth(seqs, tgt, kind, w, iters=3000, tol=1e-10):
    N = len(seqs)
    v = np.ones(N)
    lam = 0
    W = np.array(w)[kind]  # (N,4)
    for it in range(iters):
        nv = np.zeros(N)
        for d in range(4):
            ok = tgt[:, d] >= 0
            np.add.at(nv, tgt[ok, d], W[ok, d] * v[ok])
        new = nv.sum() / v.sum()
        v = nv / nv.max()
        if abs(new - lam) < tol:
            lam = new; break
        lam = new
    return lam


if __name__ == '__main__':
    cs, ct = float(sys.argv[1]), float(sys.argv[2])
    m1, m2 = int(sys.argv[3]), int(sys.argv[4])
    xs, xt = 1 / min(cs, 1), 1 / min(ct, 1)
    for m in range(m1, m2 + 1):
        seqs = windows(m)
        tgt, kind = transitions(seqs)
        g_pre = growth(seqs, tgt, kind, (xs / 3, xt / 3, 1 / 5))
        g_free = growth(seqs, tgt, kind, (1 / 3, 1 / 3, 1 / 5))
        g_cnt = growth(seqs, tgt, kind, (1, 1, 1))
        print(f"m={m:2d} states={len(seqs):7d} mu_m={g_cnt:.5f} growth_pre={g_pre:.5f} growth_free={g_free:.5f}", flush=True)
