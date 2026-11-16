"""Independent, standard-library-only checks for R6. All writes stay in R6."""
import ast
import collections
from fractions import Fraction as F
import itertools
import json
from pathlib import Path

B = Path('/Users/paronow/aklt-lean/bundle')
P = json.loads((B / 'programs/data/pext/pext7962.json').read_text())
V = (0, 0)
E, N, W, S = (1, 0), (0, 1), (-1, 0), (0, -1)
D1 = (E, N, W, S)
CORN = ((1, 1), (-1, 1), (-1, -1), (1, -1))
TIPS = {x: (2*x[0], 2*x[1]) for x in D1}
RING = (E, CORN[0], N, CORN[1], W, CORN[2], S, CORN[3])

def edge(a, b):
    return tuple(sorted((tuple(a), tuple(b))))

def neighbors(x):
    return [(x[0]+dx, x[1]+dy) for dx, dy in ((1,0),(0,1),(-1,0),(0,-1))]

def canonical(kinds, bonds, out):
    def key(mirror):
        tr = lambda x: (-x[0], x[1]) if mirror else x
        return (tr(out), tuple(sorted((tr(x), k) for x, k in kinds.items())),
                tuple(sorted(edge(tr(a), tr(b)) for a, b in bonds)))
    if out == N:
        return min(key(False), key(True))
    return key(out == W)

def unpack(r):
    return ({ast.literal_eval(x): k for x, k in r['kinds'].items()},
            {edge(a,b) for a,b in r['present']}, tuple(r['out']))

def enumerate_patterns():
    opts = []
    for x in D1:
        if x == S:
            opts.append([('x', set())] + [('d', {edge(x,z) for z in zs})
                        for zs in itertools.combinations([z for z in neighbors(x) if z != V], 2)])
        else:
            opts.append([('u', {edge(x,z) for z in neighbors(x)}), ('x', set())] +
                        [('d', {edge(x,V), edge(x,z)}) for z in neighbors(x) if z != V])
    reps = set()
    raw_compressed = raw_full = 0
    full_by_out = collections.Counter()
    full_fixed_straight = 0
    for ds in itertools.product(*opts):
        d = dict(zip(D1, ds))
        co = []
        for x in CORN:
            nb = [z for z in neighbors(x) if z in D1]
            a,b = [edge(x,z) for z in nb]
            choices = [('u', {a,b}, 1), ('x', set(), 1), ('d', {a,b}, 1),
                       ('d', {a}, 2), ('d', {b}, 2), ('d', set(), 1)]
            co.append([(kind, keep, mult) for kind, keep, mult in choices
                       if kind == 'x' or all(d[z][0] == 'x' or
                          ((edge(x,z) in keep) == (edge(x,z) in d[z][1])) for z in nb)])
        for cs in itertools.product(*co):
            kinds = {x: k for x,(k,_) in d.items()}
            keep = {x: ks for x,(_,ks) in d.items()}
            mult = 1
            for x,(k,ks,m) in zip(CORN, cs):
                kinds[x] = k; keep[x] = ks; mult *= m
            bonds = set()
            for x in D1:
                if kinds[x] == 'x':
                    continue
                for z in neighbors(x):
                    b = edge(x,z)
                    if b not in keep[x]:
                        continue
                    if z == V or z == TIPS[x] or (kinds[z] != 'x' and b in keep[z]):
                        bonds.add(b)
            live = {z for b in bonds for z in b}
            kk = {x:k for x,k in kinds.items() if x in live}
            for out in (N,E):
                if edge(V,out) in bonds:
                    raw_compressed += 1; raw_full += mult
                    full_by_out[out] += mult
                    if out == N:
                        refl = lambda z: (-z[0],z[1])
                        symmetric = all(kinds[x] == kinds[refl(x)] and
                            {edge(refl(a),refl(b)) for a,b in keep[x]} == keep[refl(x)] for x in kinds)
                        if symmetric:
                            full_fixed_straight += cs[0][2] * cs[3][2]
                    reps.add(canonical(kk, bonds, out))
    stored = {canonical(*unpack(r)) for r in P}
    print('ENUMERATION', 'raw compressed', raw_compressed, 'raw with outside kept-leg choices', raw_full,
          'classes',len(reps), 'stored classes',len(stored), 'missing',len(reps-stored), 'extra',len(stored-reps))
    print('FULL CONFIGURATION ORBITS', (full_by_out[N]+full_fixed_straight)//2+full_by_out[E],
          'raw by out',dict(full_by_out),'fixed straight',full_fixed_straight)
    assert reps == stored and len(stored) == len(P)

def rho(kind, fields):
    r = list(fields)
    assert len(r) <= 3 and all(0 <= x <= 1 for x in r)
    r += [F(0)] * (3-len(r))
    a,b,c = r
    return ((a+b+c)/3+a*b*c/5) / (1+(a*b+a*c+b*c)/3 + (F(2,3) if kind == 'd' else 0))

def roots(r):
    kinds, bonds, out = unpack(r)
    adj = collections.defaultdict(set)
    for a,b in bonds:
        if V not in (a,b):
            adj[a].add(b); adj[b].add(a)
    kinds.pop(V,None)
    for tip in TIPS.values():
        if tip in adj:
            kinds[tip] = 'u'
    alive = set(kinds)
    fields = {x: [F(1)] * (3 if x in TIPS.values() else 2 if x in CORN else 0) for x in alive}
    while True:
        x = next((x for x in sorted(alive) if x not in (E,N,W) and len(adj[x] & alive) <= 1), None)
        if x is None:
            break
        nb = adj[x] & alive
        alive.remove(x)
        if nb:
            parent = next(iter(nb))
            fields[parent].append(rho(kinds[x], fields[x]))
    if any(adj[x] & alive for x in alive):
        return None
    return {x: rho(kinds[x],fields[x]) if x in alive else F(0) for x in (E,N,W)}

def test_closed(rad, out, c):
    f,g = [x for x in (E,N,W) if x != out]
    ro,rf,rg = rad[out],rad[f],rad[g]
    a = rf*rg; k = a*(F(1,3)-c/5)
    L = lambda t: 1-c+k*t
    q2 = k*k; q1 = 2*(1-c)*k-2*a*ro*ro/9
    q0 = (1-c)**2-ro*ro*(rf*rf+rg*rg)/9
    Q = lambda t: q0+q1*t+q2*t*t
    ts = [F(-1), F(1)]
    if q2:
        t = -q1/(2*q2)
        if -1 < t < 1:
            ts.append(t)
    return all(L(t) >= 0 for t in (-1,1)) and all(Q(t) >= 0 for t in ts)

def check_operator_metadata(rec):
    kinds,bonds,out = unpack(P[rec['pid']])
    groups = []
    slot = 0
    states = {(0,0): 1}
    singles = 0
    for x in RING:
        if x in D1:
            size = int(edge(x,TIPS[x]) in bonds)
        else:
            degree = sum(x in b for b in bonds)
            size = (1 if degree == 1 and rec['leafred'] else 2) if degree else 0
        if size == 0:
            continue
        group = set(range(slot,slot+size))
        slot += size
        assert not (group & set(rec['S'])) or group <= set(rec['S'])
        if size == 1:
            choices = [(1,0),(-1,0)]; singles += 1
        else:
            choices = [(2,0),(0,0),(-2,0)]
            if kinds[x] == 'd':
                choices.append((0,1))
        new = collections.Counter()
        for (charge,parity),multiplicity in states.items():
            for w,p in choices:
                new[charge+w,2*parity+p] += multiplicity
        states = new
    assert slot == rec['n'] and all(0 <= i < slot for i in rec['S']) and len(set(rec['S'])) == len(rec['S'])
    central = singles % 2
    expected = sorted((central+1000*p, n, True) for (w,p),n in states.items() if w == central)
    stored = sorted(tuple(s) for s in rec['sectors'])
    assert sum(s[1] for s in expected) == sum(s[1] for s in stored), (rec['pid'],expected,stored)
    return expected == stored

def check_files():
    for name in ('certificates_covered.jsonl','certificates_covered_operator_only.jsonl'):
        rs = [json.loads(l) for l in (B/'programs/h1-local/out'/name).read_text().splitlines()]
        assert sorted(r['pid'] for r in rs) == list(range(len(P)))
        assert all(r['model'] == 'covered' and r['tiprad'] == '3/5' and
                   r['target'] == ('961/1000' if P[r['pid']]['out'] == [0,1] else '187/200') and
                   r['out'] == P[r['pid']]['out'] for r in rs)
        print('FILE',name,'coverage/threshold/model/radius OK',collections.Counter(r['kind'] for r in rs))
        sector_matches = collections.Counter()
        for rec in rs:
            if rec['kind'] == 'operator':
                sector_matches[check_operator_metadata(rec)] += 1
        print('FILE',name,'operator group/inversion/total central-sector dimensions OK; exact split metadata matches',dict(sector_matches))
        if name == 'certificates_covered.jsonl':
            for rec in rs:
                rad = roots(P[rec['pid']])
                assert (rad is not None) == (rec['kind'] == 'closed')
                if rad is not None:
                    assert test_closed(rad,tuple(rec['out']),F(rec['target']))
                    for x,v in rec['radii'].items():
                        assert rad[ast.literal_eval(x)] == F(v)
    count = collections.Counter()
    max_unred = (0,None); max_red = (0,None)
    for r in P:
        kinds,bonds,out = unpack(r)
        n = sum(edge(x,t) in bonds for x,t in TIPS.items())
        for x in CORN:
            n += 2*any(x in b for b in bonds)
        if n > max_unred[0]:
            max_unred = (n,r['pid'])
        nr = n - sum(1 for x in CORN if sum(x in b for b in bonds) == 1)
        if nr > max_red[0]:
            max_red = (nr,r['pid'])
        rad = roots(r)
        if rad is not None:
            count['straight' if out == N else 'turn'] += 1
    print('DECOUPLED',dict(count),'max dimensions unreduced/reduced',max_unred,max_red)
    tight = [(N,F(3825127,3979368)),(E,F(1071655,1145463)),(E,F(416114,444675))]
    for out,c in tight:
        hits = []
        for r in P:
            if tuple(r['out']) != out:
                continue
            rad = roots(r)
            if rad is not None and test_closed(rad,out,c) and not test_closed(rad,out,c+F(1,10**12)):
                f,g = [x for x in (E,N,W) if x != out]
                attained = (1+rad[f]*rad[g]/3-rad[out]*(rad[f]+rad[g])/3)/(1+rad[f]*rad[g]/5)
                assert attained == c
                hits.append((r['pid'],{str(x):str(v) for x,v in rad.items()}))
        print('TIGHT VALUE',str(c),float(c),'matches',hits)

if __name__ == '__main__':
    enumerate_patterns()
    check_files()
