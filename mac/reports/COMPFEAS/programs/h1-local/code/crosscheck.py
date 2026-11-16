"""Cross-check of the exact integer coefficient tensors (cert.py, Pauli moment tensors) against the frame engine
(ring.py, 12-point icosahedral integration) at random unit vectors, for every pattern in both slot models."""
import sys, json
import numpy as np
sys.path.insert(0, '/home/user/otis-claude/research/aklt-gap/agents/70-local-bounds/code')
from ring import load
from cert import Certificate, net_to_ring

P = load()
rng = np.random.default_rng(7)
step = int(sys.argv[1]) if len(sys.argv) > 1 else 1
worst = 0.0; cnt = 0
for refined in (False, True):
    for r in P[::step]:
        c = Certificate(r, refined=refined)
        p = c.p
        if c.n == 0:
            continue
        Un = rng.normal(size=(c.n, 3)); Un /= np.linalg.norm(Un, axis=1, keepdims=True)
        U = net_to_ring(c, Un)
        d = abs(c.evaluate(Un) - p.ratio(U))
        worst = max(worst, d); cnt += 1
print('patterns x models checked:', cnt, ' max |integer-tensor ratio - frame-engine ratio| =', worst)
