"""Float scan of the inversion certificate over the linked patterns (refined model).
Usage: run_scan.py part nparts outfile.  For each pattern: numerical minimiser -> minus group S -> c_S (float)."""
import sys, json, os, time
import numpy as np
sys.path.insert(0, '/home/user/otis-claude/research/aklt-gap/agents/70-local-bounds/code')
from ring import load
from cert import Certificate, minus_group

part, nparts, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
P = load()
ref = {r['pid']: r for r in json.load(open('/home/user/otis-claude/research/aklt-gap/agents/70-local-bounds/out/refined_linked.json'))}
todo = sorted(ref, key=lambda k: (ref[k]['ref'] - (0.961 if ref[k]['out'] == [0, 1] else 0.935)))
todo = [pid for i, pid in enumerate(todo) if i % nparts == part]
done = set()
if os.path.exists(out):
    done = set(json.loads(l)['pid'] for l in open(out))
f = open(out, 'a')
for pid in todo:
    if pid in done:
        continue
    t = time.time()
    c = Certificate(P[pid])
    val, Un, Sset = minus_group(c, restarts=2, seed=pid)
    if c.n == 0:
        lam = val
    else:
        lam, flags = c.c_S(Sset)
    f.write(json.dumps(dict(pid=pid, out=list(c.p.out), n=c.n, ref=ref[pid]['ref'], val=float(val), S=list(Sset),
                            cS=None if lam is None else float(lam), t=round(time.time() - t, 2))) + '\n')
    f.flush()
