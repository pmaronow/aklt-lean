"""Post-process realisable-pattern minima (agent 57): worst constants per step type, separating patterns realisable
only with the start site in the template.  Usage: post.py result1.json [result2.json ...]"""
import sys, json
import realizable as RZ
from realizable import canon, CORN, D1, TIPS, V, nbrs, bkey
TSET = set([V] + D1 + CORN + TIPS)
def key_of(kinds, absent, out):
    a = frozenset(b for b in absent if b[0] in TSET and b[1] in TSET)
    k = dict(kinds)
    for c in CORN:
        if k[c] == 'd' and not [y for y in nbrs(c) if y in D1 and bkey(c, y) not in absent]:
            k[c] = 'c'
    return canon(k, a, out)
nonstart = set(); allkeys = set()
for extra in (False, True):
    RZ.EXTRA = extra
    for kinds, absent, st in RZ.enumerate_realizable(with_start=True):
        for out in [(0, 1), (1, 0)]:
            kk = key_of(kinds, absent, out)
            allkeys.add(kk)
            if not st:
                nonstart.add(kk)
res = []
for f in sys.argv[1:]:
    res += json.load(open(f))
print('results', len(res), 'distinct keys known', len(allkeys), 'non-start keys', len(nonstart))
import ast
for typ, out in [('straight', (0, 1)), ('turn', (1, 0))]:
    rows = []
    for r in res:
        if tuple(r['out']) != out:
            continue
        kinds = {ast.literal_eval(x): c for x, c in r['kinds'].items()}
        absent = frozenset(tuple(map(tuple, b)) for b in r['absent'])
        kk = canon(kinds, absent, out)
        rows.append((r['min'], kk in nonstart, r['spread'], r['K'], kinds, absent))
    rows.sort(key=lambda t: t[0])
    ns = [t for t in rows if t[1]]
    st = [t for t in rows if not t[1]]
    print(f"{typ}: {len(rows)} patterns ({len(ns)} without start); worst overall {rows[0][0]:.5f}; "
          f"worst without start {ns[0][0]:.5f}; worst start-only {st[0][0] if st else float('nan'):.5f}; max spread {max(t[2] for t in rows):.1e}")
    for t in ns[:6]:
        print('   no-start', round(t[0], 5), 'K', t[3], {x: c for x, c in t[4].items() if c != 'u'},
              sorted(b for b in t[5] if V not in b))
