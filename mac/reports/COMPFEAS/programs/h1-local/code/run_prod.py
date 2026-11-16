"""Production run of the inversion certificate over the linked patterns.
Usage: run_prod.py part nparts outfile model [float]      model = covered | refined
For each linked pattern: numerical minimiser -> S (minus group; if the float bound is below the target, a greedy
search over S) -> float bound c_S -> exact Bareiss certificate at (961/1000 straight, 187/200 turn) on the sector of
least |S^z| (Lemma 6.1).  With the 5th argument 'float' the exact step is skipped."""
import sys, json, os, time
import numpy as np
sys.path.insert(0, '/home/user/otis-claude/research/aklt-gap/agents/70-local-bounds/code')
from ring import load, RING
from cert import Certificate, minus_group, Net
from ring import Pattern
from closed_exact import radii_exact

part, nparts, out, model = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3], sys.argv[4]
floatonly = len(sys.argv) > 5 and sys.argv[5] == 'float'
refined = (model == 'refined')
P = load()
TGT = {(0, 1): (961, 1000), (1, 0): (187, 200)}
if len(sys.argv) > 7:           # run_prod.py part nparts out model exact|float ps/qs pt/qt
    TGT = {(0, 1): tuple(map(int, sys.argv[6].split('/'))), (1, 0): tuple(map(int, sys.argv[7].split('/')))}
todo = []
for r in P:
    c0 = Certificate.__new__(Certificate)
    from ring import Pattern
    p = Pattern(r, refined=refined)
    if radii_exact(p)[0] != (os.environ.get('WHICH', 'linked') == 'decoupled'):
        continue                    # WHICH=decoupled: operator certificates for the decoupled patterns as well
    todo.append((r['min57'] - (0.961 if tuple(r['out']) == (0, 1) else 0.935), r['pid']))

todo.sort()
todo = [pid for i, (_, pid) in enumerate(todo) if i % nparts == part]
done = set()
if os.path.exists(out):
    done = set(json.loads(l)['pid'] for l in open(out))
f = open(out, 'a')


def groups(c):
    return [tuple(c.net.site_slots[x]) for x in RING if c.net.site_slots[x]]


def attempt(pid, leafred, seed, search=True):
    c = Certificate(P[pid], refined=refined, leafred=leafred)
    pq = TGT[c.p.out]
    tgt = pq[0] / pq[1]
    val, Un, Sset = minus_group(c, restarts=(2 if search else 1), seed=seed, sweeps=(400 if search else 80), tol=(1e-13 if search else 1e-9))
    lam, flags = c.c_S(Sset)
    tries = 1
    print('  pid', pid, 'leafred', leafred, 'n', c.n, 'val %.6f' % val, 'c_S %.6f' % (lam if lam is not None else -1), flush=True)
    if search and lam is not None and lam < tgt + 2e-6:
        # greedy search over S: flip one site group at a time while the float bound improves (at most 2 passes)
        G = groups(c)
        cur = set(Sset); best = lam
        for sweep in range(2):
            improved = False
            for g in G:
                trial = set(cur) ^ set(g)
                l2, _ = c.c_S(tuple(sorted(trial)))
                tries += 1
                if l2 is not None and l2 > best + 1e-9:
                    best, cur, improved = l2, trial, True
            if not improved or best >= tgt + 2e-6:
                break
        lam, Sset = best, tuple(sorted(cur))
        print('     after search: c_S %.6f tries %d' % (lam, tries), flush=True)
    return c, pq, tgt, val, Sset, lam, tries


for pid in todo:
    if pid in done:
        continue
    t = time.time()
    best = None
    # order of attempts: leaf-reduced without search, unreduced without search (if different and small), then searches
    plans = [(True, False), (False, False), (True, True), (False, True)]
    nun = Net(Pattern(P[pid], refined=refined), leafred=False).n
    nred = Net(Pattern(P[pid], refined=refined), leafred=True).n
    for leafred, search in plans:
        if not leafred and (nun == nred or nun > 11):
            continue
        c, pq, tgt, val, Sset, lam, tries = attempt(pid, leafred, pid, search)
        if best is None or (lam is not None and (best[5] is None or lam > best[5])):
            best = (c, pq, tgt, val, Sset, lam, tries, leafred)
        if lam is not None and lam >= tgt + 2e-6:
            break
    c, pq, tgt, val, Sset, lam, tries, leafred = best
    rec = dict(pid=pid, out=list(c.p.out), n=c.n, leafred=leafred, min57=P[pid]['min57'], val=float(val), S=list(Sset),
               cS=None if lam is None else float(lam), tries=tries, target='%d/%d' % pq)
    if lam is not None and lam >= tgt + 2e-6 and not floatonly:
        res = c.exact(Sset, pq[0], pq[1], least_only=True)
        rec['status'] = 'CERTIFIED' if res['ok'] else 'EXACT_FAILED'
        rec['sectors'] = res['sectors']
    elif floatonly:
        rec['status'] = 'FLOAT_OK' if (lam is not None and lam >= tgt + 2e-6) else 'FLOAT_BELOW'
    else:
        rec['status'] = 'BELOW_TARGET'
    rec['t'] = round(time.time() - t, 2)
    print('pid', pid, rec['status'], rec['t'], flush=True)
    f.write(json.dumps(rec) + '\n'); f.flush()
