"""Enumerate the local patterns seen by a first-visit step: restriction of the trail's past to the radius-2 template
around v (site kinds + trail bonds inside the template), canonicalised under the 8 lattice symmetries fixing v
(together with the out direction).  Agent 57."""
import sys
from collections import Counter
DIRS = [(1, 0), (0, 1), (-1, 0), (0, -1)]
T = [(i, j) for i in range(-2, 3) for j in range(-2, 3) if abs(i) + abs(j) <= 2]
TS = set(T)
SYMS = [lambda p: (p[0], p[1]), lambda p: (-p[1], p[0]), lambda p: (-p[0], -p[1]), lambda p: (p[1], -p[0]),
        lambda p: (p[0], -p[1]), lambda p: (-p[0], p[1]), lambda p: (p[1], p[0]), lambda p: (-p[1], -p[0])]


def bkey(a, b):
    return (a, b) if a <= b else (b, a)


def canon(passes, tbonds, out):
    best = None
    for S in SYMS:
        ks = tuple(sorted((S(x), min(c, 2)) for x, c in passes.items() if x in TS and c > 0))
        bs = tuple(sorted(bkey(S(a), S(b)) for (a, b) in tbonds if a in TS and b in TS))
        key = (S(out), ks, bs)
        if best is None or key < best:
            best = key
    return best


def enumerate_patterns(L):
    """backward trails from v = (0,0) of length 0..L (length 0 = start step)."""
    pats = Counter()
    first = {}
    used = set()
    seq = [(0, 0)]

    def record():
        # seq = [v, u_1, ..., u_m]; passes: every u_i, i>=1, gets +1
        passes = {}
        for u in seq[1:]:
            passes[u] = passes.get(u, 0) + 1
        tb = set(used)
        arr = seq[1] if len(seq) > 1 else None
        for d in DIRS:
            y = d
            if arr is not None and y == arr:
                continue
            key = canon(passes, tb, y)
            pats[key] += 1
            if key not in first:
                first[key] = (list(reversed(seq)), y)

    def dfs():
        record()
        if len(seq) - 1 == L:
            return
        x = seq[-1]
        for d in DIRS:
            y = (x[0] + d[0], x[1] + d[1])
            if y == (0, 0):
                continue
            b = bkey(x, y)
            if b in used:
                continue
            used.add(b); seq.append(y)
            dfs()
            used.discard(b); seq.pop()

    dfs()
    return pats, first


if __name__ == '__main__':
    for L in range(0, int(sys.argv[1]) + 1):
        pats, first = enumerate_patterns(L)
        print(L, 'distinct patterns', len(pats), flush=True)
