"""Independent stdlib audit of the frozen H1 data; no production imports.

All rational calculations use fractions.Fraction. Run from ADJ-R6:
  python3 audit_math.py
"""
import ast
import collections
import itertools as it
import json
from fractions import Fraction as F
from pathlib import Path

BUNDLE = Path('/home/ubuntu/aklt/manuscript/bundle')
DATA = BUNDLE / 'programs/data/pext/pext7962.json'
OUT = BUNDLE / 'programs/h1-local/out'
Y = (0, 0)
E, N, W, S = (1, 0), (0, 1), (-1, 0), (0, -1)
D1 = (E, N, W, S)
CORNERS = ((1, 1), (-1, 1), (-1, -1), (1, -1))
TIPS = {x: (2*x[0], 2*x[1]) for x in D1}
RING = (E, CORNERS[0], N, CORNERS[1], W, CORNERS[2], S, CORNERS[3])


def nb(x):
    a, b = x
    return ((a+1, b), (a-1, b), (a, b+1), (a, b-1))


def bond(a, b):
    return tuple(sorted((a, b)))


def parse(r):
    return (tuple(r['out']), {ast.literal_eval(x): k for x, k in r['kinds'].items()},
            frozenset(bond(tuple(a), tuple(b)) for a, b in r['present']))


def key(out, kinds, edges):
    def form(reflect):
        def f(x):
            return (-x[0], x[1]) if reflect else x
        return (f(out), tuple(sorted((f(x), k) for x, k in kinds.items())),
                tuple(sorted(bond(f(a), f(b)) for a, b in edges)))
    if out == E:
        return form(False)
    if out == W:
        return form(True)
    return min(form(False), form(True))


def options(x):
    ns = set(nb(x))
    if x == S:
        return [('x', frozenset())] + [('d', frozenset(z)) for z in it.combinations(sorted(ns-{Y}), 2)]
    # Consistency with the live centre, which keeps its E,N,W bonds,
    # forces every non-removed D neighbour to retain its bond to Y.
    ds = [frozenset(z) for z in it.combinations(sorted(ns), 2) if x not in D1 or Y in z]
    return [('u', frozenset(ns)), ('x', frozenset())] + [('d', z) for z in ds]


def enumerate_patterns():
    raw, reps = 0, set()
    for base in it.product(*(options(x) for x in D1)):
        st = dict(zip(D1, base))
        compatible = []
        for z in CORNERS:
            os = []
            for kind, keep in options(z):
                if all(kind == 'x' or st[x][0] == 'x' or ((x in keep) == (z in st[x][1]))
                       for x in D1 if x in nb(z)):
                    os.append((kind, keep))
            compatible.append(os)
        for cs in it.product(*compatible):
            raw += 1
            status = dict(st, **{})
            status.update(zip(CORNERS, cs))
            edges = set()
            for x in D1:
                k, keep = status[x]
                if k == 'x':
                    continue
                if x != S:
                    edges.add(bond(Y, x))
                if TIPS[x] in keep:
                    edges.add(bond(x, TIPS[x]))
                for z in CORNERS:
                    if z in keep and status[z][0] != 'x' and x in status[z][1]:
                        edges.add(bond(x, z))
            live = set(it.chain.from_iterable(edges))
            kinds = {x: k for x, (k, keep) in status.items() if x in live}
            for out in (E, N, W):
                if bond(Y, out) in edges:
                    reps.add(key(out, kinds, edges))
    return raw, reps


def groups(r, reduced):
    _, kinds, edges = parse(r)
    gr = []
    for x in RING:
        if x in D1:
            if bond(x, TIPS[x]) in edges:
                gr.append(('single', x))
        else:
            degree = sum(x in b for b in edges)
            if degree:
                gr.append(('single' if reduced and degree == 1 else kinds[x]+'pair', x))
    return gr


def block_dimensions(gr):
    d = sum(t == 'dpair' for t, x in gr)
    central = sum(t == 'single' for t, x in gr) % 2
    dims = []
    for eps in it.product((1, -1), repeat=d):
        signs = iter(eps)
        weights = {0: 1}
        for t, x in gr:
            ws = (1, -1) if t == 'single' else (2, 0, -2)
            if t == 'dpair' and next(signs) == -1:
                ws = (0,)
            new = collections.Counter()
            for a, n in weights.items():
                for b in ws:
                    new[a+b] += n
            weights = new
        dims.append(weights.get(central, 0))
    return dims


def rho(kind, rs):
    assert len(rs) <= 3
    a, b, c = list(map(F, rs)) + [F(0)]*(3-len(rs))
    return ((a+b+c)/3 + a*b*c/5) / (1+(a*b+a*c+b*c)/3 + (F(2, 3) if kind == 'd' else 0))


def prune(r):
    out, kinds, edges = parse(r)
    roots = {x for x in (E, N, W) if bond(x, Y) in edges}
    adj = collections.defaultdict(set)
    for a, b in edges:
        if Y not in (a, b):
            adj[a].add(b)
            adj[b].add(a)
    alive = (set(it.chain.from_iterable(edges)) - {Y}) | roots
    fields = {x: ([F(1)]*2 if x in CORNERS else [F(1)]*3 if x in TIPS.values() else []) for x in alive}
    # Integrate actual tip spins, not a preloaded 3/5 message.
    while True:
        leaves = sorted(x for x in alive-roots if len(adj[x] & alive) <= 1)
        if not leaves:
            break
        for x in leaves:
            parent = adj[x] & alive
            alive.remove(x)
            if parent:
                p = next(iter(parent))
                fields[p].append(rho(kinds.get(x, 'u'), fields[x]))
    if any(adj[x] & alive for x in alive):
        return None
    return {x: rho(kinds[x], fields[x]) for x in roots}


def scalar_test(ro, rf, rg, c):
    a = rf*rg
    k = (F(1, 3)-c/5)*a
    l0 = 1-c
    q0 = l0*l0 - ro*ro*(rf*rf+rg*rg)/9
    q1 = 2*l0*k - 2*a*ro*ro/9
    q2 = k*k
    candidates = [F(-1), F(1)]
    if q2:
        t = -q1/(2*q2)
        if -1 < t < 1:
            candidates.append(t)
    return (min(l0-k, l0+k) >= 0 and min(q0+q1*t+q2*t*t for t in candidates) >= 0)


def mean_collinear(rs):
    # Direct one-dimensional sphere integral: E[z^(2j)] = 1/(2j+1).
    poly = [F(1)]
    for r in rs:
        new = [F(0)]*(len(poly)+1)
        for j, a in enumerate(poly):
            new[j] += a
            new[j+1] += a*r
        poly = new
    den = sum(a/F(j+1) for j, a in enumerate(poly) if j % 2 == 0)
    num = sum(a/F(j+2) for j, a in enumerate(poly) if j % 2 == 1)
    return num/den


def main():
    records = json.loads(DATA.read_text())
    assert [r['pid'] for r in records] == list(range(7962))
    raw, expected = enumerate_patterns()
    actual = {key(*parse(r)) for r in records}
    print('ENUM raw configurations:', raw)
    print('ENUM effective:', len(expected), 'straight:', sum(k[0] == N for k in expected),
          'turn:', sum(k[0] == E for k in expected))
    print('ENUM records:', len(records), 'distinct:', len(actual), 'missing:', len(expected-actual), 'extra:', len(actual-expected))
    assert expected == actual and len(actual) == len(records)
    for label, out in (('straight', N), ('turn', E)):
        smallest = min((r for r in records if tuple(r['out']) == out), key=lambda r: r['min57'])
        print('NUMERICAL stored minimum:', label, 'pid', smallest['pid'], 'min57', smallest['min57'])

    unreduced = [sum(1 if t == 'single' else 2 for t, x in groups(r, False)) for r in records]
    reduced = [sum(1 if t == 'single' else 2 for t, x in groups(r, True)) for r in records]
    print('DIM all records: max unreduced', max(unreduced), 'max reduced', max(reduced),
          'unreduced=12 records', sum(n == 12 for n in unreduced))
    print('DIM pid 113:', 'unreduced', unreduced[113], 'reduced', reduced[113], 'groups', groups(records[113], False))
    maxima = 0
    historical = 0
    nblocks = 0
    certsets = {}
    for fn in ('certificates_covered_operator_only.jsonl', 'certificates_covered.jsonl'):
        cs = [json.loads(l) for l in (OUT/fn).read_text().splitlines()]
        assert sorted(c['pid'] for c in cs) == list(range(7962))
        assert all(F(c['target']) == (F(961, 1000) if tuple(records[c['pid']]['out']) == N else F(187, 200))
                   and c['model'] == 'covered' and c['tiprad'] == '3/5' for c in cs)
        ops = [c for c in cs if c['kind'] == 'operator']
        for c in ops:
            gr = groups(records[c['pid']], c['leafred'])
            assert c['n'] == sum(1 if t == 'single' else 2 for t, x in gr)
            n = c['n']
            assert len(c['S']) == len(set(c['S'])) and all(0 <= i < n for i in c['S'])
            i = 0
            for kind, x in gr:
                if kind != 'single':
                    assert (i in c['S']) == (i+1 in c['S'])
                i += 1 if kind == 'single' else 2
        certsets[fn] = {c['pid']: c for c in cs}
        print('CERT', fn, 'coverage/threshold/model/tipradius/inversion groups: PASS;',
              'operator', len(ops), 'closed', len(cs)-len(ops),
              'unreduced', [(c['pid'], c['n']) for c in ops if not c['leafred']],
              'max selected n', max(c['n'] for c in ops))
        if fn.endswith('operator_only.jsonl'):
            for c in ops:
                ds = block_dimensions(groups(records[c['pid']], c['leafred']))
                maxima = max(maxima, max(ds))
                nblocks += len(ds)
                saved = sorted(s[1] for s in c['sectors'])
                if saved != sorted(ds):
                    assert saved == [sum(ds)]
                    historical += 1
                if c['pid'] in (711, 3596, 7725):
                    print('BLOCK pid', c['pid'], 'split dimensions', ds, 'stored', saved)
            print('BLOCK max selected:', maxima, 'central exchange blocks:', nblocks, 'combined diagnostics:', historical)
    mixed = certsets['certificates_covered.jsonl']
    operator = certsets['certificates_covered_operator_only.jsonl']
    assert all((c['leafred'], c['S']) == (operator[i]['leafred'], operator[i]['S'])
               for i, c in mixed.items() if c['kind'] == 'operator')

    dec = {}
    counts = collections.Counter()
    for r in records:
        rad = prune(r)
        if rad is None:
            assert mixed[r['pid']]['kind'] == 'operator'
            continue
        out = tuple(r['out'])
        rf, rg = [rad.get(x, F(0)) for x in (E, N, W) if x != out]
        assert scalar_test(rad[out], rf, rg, F(961, 1000) if out == N else F(187, 200))
        c = mixed[r['pid']]
        assert c['kind'] == 'closed'
        assert {ast.literal_eval(x): F(v) for x, v in c['radii'].items()} == rad
        dec[r['pid']] = rad
        counts['straight' if out == N else 'turn'] += 1
    print('CLOSED exact H1 tests/radii:', len(dec), dict(counts), 'all PASS')
    for pid, value in ((7645, F(3825127, 3979368)), (1382, F(1071655, 1145463)), (5469, F(416114, 444675))):
        rad = dec[pid]
        out = tuple(records[pid]['out'])
        rf, rg = [rad.get(x, F(0)) for x in (E, N, W) if x != out]
        ro = rad[out]
        attained = (1+rf*rg/3-ro*(rf+rg)/3)/(1+rf*rg/5)
        assert attained == value and scalar_test(ro, rf, rg, value)
        assert not scalar_test(ro, rf, rg, value+F(1, 10**12))
        print('VALUE pid', pid, 'radii', {str(x): str(v) for x, v in rad.items()},
              'exact', value, 'attained at t=1; test at value PASS; value+1e-12 FAIL')

    tip = mean_collinear([F(1)]*3)
    corner = mean_collinear([F(1)]*2)
    rr = mean_collinear([tip, corner, corner])
    rn = mean_collinear([tip])
    ratio = (1-rr*rr/3)/(1+rr*rn/5)
    print('WITNESS direct moment messages:', 'tip', tip, 'corner', corner, 'E/W', rr, 'N', rn)
    print('WITNESS ratio:', ratio, 'decimal', float(ratio), '187/200 minus ratio', F(187, 200)-ratio)
    assert ratio == F(1040285, 1131207) < F(187, 200)
    keep = {x: set(nb(x)) for x in (E, N, W)+CORNERS}
    keep[Y] = {E, N, W}
    keep[N] = {Y, TIPS[N]}
    keep[(1, 1)].remove(N)
    keep[(-1, 1)].remove(N)
    assert all((b in keep[a]) == (a in keep[b]) for a in keep for b in nb(a) if b in keep)
    witness_edges = {bond(a, b) for a in keep for b in keep[a]
                     if b in keep or (a in D1 and b == TIPS[a])}
    witness_kinds = {x: 'u' for x in keep if x != Y}
    assert key(E, witness_kinds, witness_edges) not in actual
    print('WITNESS broad-reading consistency (C): PASS; key in frozen records: False')
    # Unit roundoff proof constants, evaluated without floating arithmetic.
    u = F(1, 2**53)
    gamma32 = 32*u/(1-32*u)
    lower = (1-u)**2*(1-gamma32)
    print('GUARD exact lower factor > 1/2:', lower > F(1, 2),
          'and > 1-1/10^12:', lower > 1-F(1, 10**12))


if __name__ == '__main__':
    main()
