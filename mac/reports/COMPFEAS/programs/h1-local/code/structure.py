"""Structural analysis of the P_ext^59 patterns after the full tree collapse (agent 70, NOTES Entry 1).
Reads agent 63's out/pext7962.json.  For each pattern: graph H = live template sites other than v with the present
bonds not touching v; v-neighbours = d1 sites with a present v-bond.  Pendant trees are pruned (each becomes a field in
a ball at its attachment node).  Reports the collapsed dimension and the cycle structure."""
import json, ast, sys, collections
P63 = '/home/user/otis-claude/research/aklt-gap/agents/63-certify-N/out/pext7962.json'
V = (0, 0)
D1 = [(1, 0), (0, 1), (-1, 0), (0, -1)]
CORNERS = [(1, 1), (-1, 1), (-1, -1), (1, -1)]
TIPS = [(2, 0), (0, 2), (-2, 0), (0, -2)]


def analyse(r):
    kinds = {ast.literal_eval(k): c for k, c in r['kinds'].items()}
    present = set(frozenset((tuple(a), tuple(b))) for a, b in r['present'])
    vn = [x for x in D1 if frozenset((V, x)) in present]
    adj = collections.defaultdict(set)
    for b in present:
        a, c = tuple(b)
        if V in (a, c):
            continue
        adj[a].add(c); adj[c].add(a)
    nodes = set(adj) | set(vn)
    # own slots: tips 3, corners 2 (if live = incident to a present bond), d1 0
    slots = {x: (3 if x in TIPS else 2 if x in CORNERS else 0) for x in nodes}
    # keep only components containing a v-neighbour
    comp = {}
    for x in vn:
        if x in comp:
            continue
        st = [x]; comp[x] = x
        while st:
            y = st.pop()
            for z in adj[y]:
                if z not in comp:
                    comp[z] = x; st.append(z)
    nodes = set(comp)
    deg = {x: len(adj[x] & nodes) for x in nodes}
    fields = {x: (1 if slots[x] else 0) if False else 0 for x in nodes}
    # a node's own slots: counted as `slots[x]` unit fields
    own = dict((x, slots[x]) for x in nodes)
    pend = {x: 0 for x in nodes}      # number of pruned pendant branches attached (each one field in a ball)
    alive = set(nodes)
    changed = True
    while changed:
        changed = False
        for x in list(alive):
            if x in vn:
                continue
            d = len(adj[x] & alive)
            if d <= 1:
                alive.discard(x); changed = True
                if d == 1:
                    y = next(iter(adj[x] & alive))
                    if own[x] + pend[x] > 0:
                        pend[y] += 1
    # dimension count
    nvec = 0
    detail = []
    for x in alive:
        d = len(adj[x] & alive)
        k = own[x] + pend[x]
        D = d + (1 if x in vn else 0)
        if k == 0:
            m = 0
        elif D <= 1:
            m = 1
        else:
            m = k
        nvec += m
        detail.append((x, d, k, m))
    dim = max(2 * nvec - 3, 0) if nvec >= 2 else 0
    # cycle rank of the pruned graph
    ne = sum(len(adj[x] & alive) for x in alive) // 2
    ncomp = 0
    seen = set()
    for x in alive:
        if x in seen:
            continue
        ncomp += 1
        st = [x]; seen.add(x)
        while st:
            y = st.pop()
            for z in adj[y] & alive:
                if z not in seen:
                    seen.add(z); st.append(z)
    cyc = ne - len(alive) + ncomp
    nb2 = sum(1 for x in alive if x in CORNERS)      # two-body corners surviving
    return dict(dim=dim, nvec=nvec, cyc=cyc, nb2=nb2, ncomp=ncomp, nedge=ne, s_alive=((0, -1) in alive), detail=detail)


if __name__ == '__main__':
    P = json.load(open(P63))
    tab = collections.Counter(); worst = {}
    rows = []
    for r in P:
        a = analyse(r)
        typ = 'S' if tuple(r['out']) == (0, 1) else 'T'
        rows.append((r['pid'], typ, r['dim'], a['dim'], a['cyc'], a['nb2'], a['nedge'], r['min57']))
        key = (typ, a['dim'], a['cyc'], a['nedge'])
        tab[key] += 1
        if key not in worst or r['min57'] < worst[key][0]:
            worst[key] = (r['min57'], r['pid'], r['dim'])
    print('type newdim cyc nedge(pruned graph) : count, worst min57 (pid, dim63)')
    for key in sorted(tab):
        print(key, tab[key], worst[key])
    json.dump(rows, open(sys.argv[1], 'w')) if len(sys.argv) > 1 else None
    # cross table dim63 -> new dim
    ct = collections.Counter((d63, nd) for _, _, d63, nd, _, _, _, _ in rows)
    print('dim63 -> newdim counts')
    for k in sorted(ct):
        print(k, ct[k])
