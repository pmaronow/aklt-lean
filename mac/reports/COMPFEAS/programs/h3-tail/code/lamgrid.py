"""Memory-10 pinned growth lambda_A (phase A weights x_s/3, x_t/3, revisit 1/5) on a grid of constants (float,
NUMERICAL; the certificate runs re-check lambda_A rigorously through the sub-invariance test).
Usage: python3 lamgrid.py"""
import sys
import numpy as np
import scipy.sparse as sp
import scipy.sparse.linalg as sla
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from memgrowth import windows, transitions

seqs = windows(10)
tgt, kind = transitions(seqs)
N = len(seqs)
rows, cols, kinds = [], [], []
for d in range(4):
    ok = tgt[:, d] >= 0
    rows.append(tgt[ok, d]); cols.append(np.nonzero(ok)[0]); kinds.append(kind[ok, d])
rows = np.concatenate(rows); cols = np.concatenate(cols); kinds = np.concatenate(kinds)
for cs in (0.970, 0.961, 0.955, 0.950):
    out = []
    for ct in (0.935, 0.932, 0.930, 0.927, 0.925):
        w = np.array([1 / cs / 3, 1 / ct / 3, 0.2])[kinds]
        M = sp.csr_matrix((w, (rows, cols)), shape=(N, N))
        val = sla.eigs(M, k=1, which='LM', return_eigenvectors=False, tol=1e-12)
        out.append(f"{ct}: {abs(val[0]):.5f}")
    print(f"c_s = {cs}: " + '  '.join(out), flush=True)
