"""Numerical minima of the linked patterns in the refined slot model (diluted corner with k present d1-bonds: 2-k slots).
Usage: run_refined.py part nparts outfile   (patterns sorted by agent 57's minimum; resumable)."""
import sys, json, os, time
sys.path.insert(0, '/home/user/otis-claude/research/aklt-gap/agents/70-local-bounds/code')
from ring import Pattern, load, C0, C1, C2, C3
from collapse import Tree

part, nparts, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
P = load()
todo = []
for r in P:
    p = Pattern(r, refined=True)
    if Tree(p).decoupled():
        continue
    todo.append((r['min57'], r['pid']))
todo.sort()
todo = [pid for i, (_, pid) in enumerate(todo) if i % nparts == part]
done = set()
if os.path.exists(out):
    for line in open(out):
        done.add(json.loads(line)['pid'])
f = open(out, 'a')
for pid in todo:
    if pid in done:
        continue
    p = Pattern(P[pid], refined=True)
    hasD = any(p.live[c] and p.kind[c] == 'd' for c in (C0, C1, C2, C3))
    t = time.time()
    if hasD:
        val, U = p.minimise(restarts=2, seed=pid)
    else:
        val = P[pid]['min57']
    f.write(json.dumps(dict(pid=pid, out=list(p.out), nv=p.nv, min57=P[pid]['min57'], ref=float(val), hasD=hasD,
                            t=round(time.time() - t, 2))) + '\n')
    f.flush()
