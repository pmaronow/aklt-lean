"""Extended pattern class P_ext of agent 59 (NOTES Entry 7.4(iii)/7.6), agent 57's reading:
radius-2 template around the first-visit step vertex v = (0,0) (uniform), arrival from s = (0,-1) (bond s-v absent);
every other template site has status U (keeps all bonds), D(K) (diluted, keeps a set K of at most 2 of its 4
bonds/legs, any K, no consistency constraint) or X (removed); a bond is present iff both ends are non-removed and
keep it.  s has status D(K) with s-v not in K, or X.  Tips are replaced by their covering (live, 3 slots; Lemma 4.3b);
corner legs are slots (Lemma 4.3a/c), so a corner is described by its kind and its present d1-bonds.
Effective pattern = (kinds of the non-removed relevant sites, set of present template bonds)."""
import itertools
from patch import bkey, nbrs
V = (0, 0); S = (0, -1)
E, N, W = (1, 0), (0, 1), (-1, 0)
D1 = [E, N, W, S]
CORN = [(1, 1), (-1, 1), (1, -1), (-1, -1)]
TIPS = [(2, 0), (0, 2), (-2, 0), (0, -2)]
TSET = set([V] + D1 + CORN + TIPS)


def d1_bonds(x):
    return [bkey(x, y) for y in nbrs(x)]           # 4 bonds: v, tip, 2 corners


def site_options(x):
    if x in CORN:
        a, b = [bkey(x, y) for y in nbrs(x) if y in D1]
        return [('u', frozenset([a, b])), ('d', frozenset([a, b])), ('d', frozenset([a])), ('d', frozenset([b])), ('x', frozenset())]
    L = d1_bonds(x)
    if x == S:
        L = [b for b in L if V not in b]
        opts = [('x', frozenset())]
        for r in (1, 2):
            for K in itertools.combinations(L, r):
                opts.append(('d', frozenset(K)))
        return opts
    opts = [('u', frozenset(L)), ('x', frozenset())]
    for r in (1, 2):
        for K in itertools.combinations(L, r):
            opts.append(('d', frozenset(K)))
    return opts


MIRROR = lambda p: (-p[0], p[1])


def effective(choice):
    """choice: dict site -> (kind, keep).  Returns (kinds of relevant live sites, present bonds)."""
    present = set()
    keep = {x: choice[x][1] for x in choice}
    alive = {x: choice[x][0] != 'x' for x in choice}
    # v keeps its three non-arrival bonds
    for x in [E, N, W]:
        b = bkey(V, x)
        if alive[x] and b in keep[x]:
            present.add(b)
    for x in D1:
        if not alive[x]:
            continue
        for y in nbrs(x):
            if y == V:
                continue
            b = bkey(x, y)
            if b not in keep[x]:
                continue
            if y in TIPS:
                present.add(b)
            elif alive[y] and b in keep[y]:
                present.add(b)
    # relevant sites: incident to a present bond (v always)
    rel = set([V])
    for b in present:
        rel |= set(b)
    kinds = {x: choice[x][0] for x in choice if x in rel}
    return kinds, frozenset(present)


def canon(kinds, present, out):
    best = None
    for f in (lambda p: p, MIRROR):
        k = tuple(sorted((f(x), c) for x, c in kinds.items()))
        a = tuple(sorted(bkey(f(b[0]), f(b[1])) for b in present))
        key = (f(out), k, a)
        if best is None or key < best:
            best = key
    return best


def enumerate_pext():
    sites = [E, N, W, S] + CORN
    opts = [site_options(x) for x in sites]
    reps = {}
    for combo in itertools.product(*opts):
        kinds, present = effective(dict(zip(sites, combo)))
        for out in [N, E]:
            if bkey(V, out) not in present:
                continue
            key = canon(kinds, present, out)
            if key not in reps:
                reps[key] = (kinds, present, out)
    return reps


if __name__ == '__main__':
    import time
    t = time.time()
    reps = enumerate_pext()
    ns = sum(1 for k in reps if reps[k][2] == N); nt = len(reps) - ns
    print('P_ext effective patterns:', len(reps), 'straight', ns, 'turn', nt, 'time', round(time.time() - t))


def site_options_consistent(x):
    """Reachable statuses in agent 59's recursion (U -> D keeping its 2 unused bonds -> X; passage site -> X):
    U keeps all; D keeps exactly 2 bonds/legs (s: 2 of its 3 non-v bonds; e, N, W: must keep the v-bond, v being
    unvisited); X anything.  Corner D: kept d1-bonds in {both, a (+leg), b (+leg), none (+2 legs)}."""
    if x in CORN:
        a, b = [bkey(x, y) for y in nbrs(x) if y in D1]
        return [('u', frozenset([a, b])), ('d', frozenset([a, b])), ('d', frozenset([a])), ('d', frozenset([b])),
                ('d', frozenset()), ('x', frozenset())]
    L = d1_bonds(x)
    if x == S:
        L = [b for b in L if V not in b]
        return [('x', frozenset())] + [('d', frozenset(K)) for K in itertools.combinations(L, 2)]
    vb = bkey(x, V)
    return [('u', frozenset(L)), ('x', frozenset())] + [('d', frozenset([vb, b])) for b in L if b != vb]


def enumerate_pext_consistent():
    """P_ext^59: consistency between non-removed sites (a bond between two non-X non-tip sites is kept by both or
    dropped by both); removed sites unconstrained; no component constraint; no start-type sites."""
    sites = [E, N, W, S] + CORN
    opts = [site_options_consistent(x) for x in sites]
    reps = {}
    for combo in itertools.product(*opts):
        ch = dict(zip(sites, combo))
        ok = True
        for x in D1:
            if ch[x][0] == 'x':
                continue
            for c in CORN:
                if c not in nbrs(x) or ch[c][0] == 'x':
                    continue
                b = bkey(x, c)
                if (b in ch[x][1]) != (b in ch[c][1]):
                    ok = False; break
            if not ok:
                break
        if not ok:
            continue
        kinds, present = effective(ch)
        for out in [N, E]:
            if bkey(V, out) not in present:
                continue
            key = canon(kinds, present, out)
            if key not in reps:
                reps[key] = (kinds, present, out)
    return reps
