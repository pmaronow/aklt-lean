"""All realisable radius-2 patterns around a first-visit step (agent 57).  v=(0,0), arrival from s=(0,-1).
Site statuses: unvisited; passed once (keeps exactly 2 of its 4 bonds/legs); passed twice (decoupled);
start site x (keeps 3).  Tips (+-2,0),(0,+-2) are always replaced by their covering (live with 3 slots), which is
exact-or-pessimistic for every tip status (the tip acts through mu in B(3/5), and 0 is in the ball).
Consistency: a bond is a trail bond iff it is dropped at both endpoints; every component of trail bonds must reach
a leg, x or v.  Output: list of (kinds, absent_bonds) for pattern_custom."""
import itertools
from patch import bkey, nbrs
V = (0, 0); S = (0, -1)
D1 = [(1, 0), (0, 1), (-1, 0), (0, -1)]
CORN = [(1, 1), (-1, 1), (1, -1), (-1, -1)]
TIPS = [(2, 0), (0, 2), (-2, 0), (0, -2)]
TS = set([V] + D1 + CORN + TIPS)
EXTRA = False


def legs(x):
    return [bkey(x, y) for y in nbrs(x)]


def statuses(x, is_s=False):
    """possible (kind, kept-bond-set, is_start) for site x."""
    L = legs(x)
    out = []
    if x in D1:
        vb = bkey(x, V)
        others = [b for b in L if b != vb]
        if is_s:
            # s: bond to v is a trail bond; passed once keeps 2 of the other 3; twice -> none; s = start keeps 3
            for keep in itertools.combinations(others, 2):
                out.append(('d', frozenset(keep), False))
            out.append(('c', frozenset(), False))
            out.append(('d', frozenset(others), True))
            if EXTRA:
                for keep in others:   # s = start passed twice: keeps one non-v bond, site decoupled
                    out.append(('c', frozenset([keep]), True))
        else:
            out.append(('u', frozenset(L), False))
            for keep in others:
                out.append(('d', frozenset([vb, keep]), False))
            for keep in itertools.combinations(others, 2):
                out.append(('d', frozenset((vb,) + keep), True))
            if EXTRA:   # start passed twice: all three non-v bonds used, site decoupled
                out.append(('c', frozenset([vb]), True))
    else:  # corner
        out.append(('u', frozenset(L), False))
        for keep in itertools.combinations(L, 2):
            out.append(('d', frozenset(keep), False))
        out.append(('c', frozenset(), False))
        for keep in itertools.combinations(L, 3):
            out.append(('d', frozenset(keep), True))
        if EXTRA:
            for keep in L:
                out.append(('c', frozenset([keep]), True))
    return out


def enumerate_realizable(with_start=False):
    sites = [(1, 0), (0, 1), (-1, 0), S] + CORN
    choices = [statuses(x, is_s=(x == S)) for x in sites]
    res = []
    for combo in itertools.product(*choices):
        if sum(c[2] for c in combo) > 1:
            continue
        st = dict(zip(sites, combo))
        # trail bonds: for each bond incident to a non-tip site, dropped iff not kept; check consistency
        ok = True
        tb = set()
        for x in sites:
            for b in legs(x):
                dropped = b not in st[x][1]
                y = b[0] if b[1] == x else b[1]
                if y == V:
                    # bond to v: a trail bond only for s
                    if dropped != (x == S):
                        ok = False; break
                    continue
                if y in st:
                    dy = b not in st[y][1]
                    if dy != dropped:
                        ok = False; break
                if dropped:
                    tb.add(b)
            if not ok:
                break
        if not ok:
            continue
        # passed-twice / start bookkeeping already in statuses; component check: every component of trail bonds
        # inside the radius-2 template reaches a leg leaving it, the start, or v
        comp_ok = True
        adj = {}
        for (a, b) in tb:
            adj.setdefault(a, []).append(b); adj.setdefault(b, []).append(a)
        seen = set()
        for x0 in adj:
            if x0 in seen:
                continue
            stack = [x0]; comp = set()
            while stack:
                y = stack.pop()
                if y in comp:
                    continue
                comp.add(y); stack.extend(adj.get(y, []))
            seen |= comp
            good = any(y not in TS or y in TIPS or y == V or (y in st and st[y][2]) for y in comp)
            if not good:
                comp_ok = False; break
        if not comp_ok:
            continue
        kinds = {x: st[x][0] for x in sites}
        kinds[(0, -2)] = 'u'
        absent = set(b for b in tb)
        absent.add(bkey(V, S))
        res.append((kinds, frozenset(absent), any(c[2] for c in combo)) if with_start else (kinds, frozenset(absent)))
    return res


MIRROR = lambda p: (-p[0], p[1])


def canon(kinds, absent, out):
    best = None
    for f in (lambda p: p, MIRROR):
        k = tuple(sorted((f(x), c) for x, c in kinds.items()))
        a = tuple(sorted(bkey(f(b[0]), f(b[1])) for b in absent))
        key = (f(out), k, a)
        if best is None or key < best:
            best = key
    return best


if __name__ == '__main__':
    R = enumerate_realizable()
    print('realisable configurations', len(R))
    for out in [(0, 1), (1, 0)]:
        keys = set()
        for kinds, absent in R:
            keys.add(canon(kinds, absent, out))
        print('out', out, 'distinct up to mirror', len(keys))
