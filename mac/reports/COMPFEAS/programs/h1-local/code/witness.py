"""Operator (entanglement-witness) certificates for the level-1 step inequalities (agent 70, NOTES Entry 3-4).

F(m) = Z_cur(m) - c Z_next(m) is multi-affine in the unit vectors m_i, so F(m) = <m|W_cur - c W_next|m> for product
coherent states, W_X = sum_alpha f^X_alpha sigma^alpha (f = multi-affine coefficients).  For a set S of qubits the
partial transpose W^{T_S} (sign flip of the y-components of the slots in S) has the same values on product states;
c_S := min generalised eigenvalue of (W_cur^{T_S}, W_next^{T_S}) is a rigorous lower bound for inf_m Z_cur/Z_next
once the PSD check is done in exact/interval arithmetic."""
import sys, itertools
import numpy as np
import scipy.linalg as sla
sys.path.insert(0, '/home/user/otis-claude/research/aklt-gap/agents/70-local-bounds/code')
from ring import Pattern, load, FR, GR, BOND, ONES, RING, E, N, W, S, C0, C1, C2, C3

PAULI = np.zeros((4, 2, 2), complex)
PAULI[0] = np.eye(2); PAULI[1] = [[0, 1], [1, 0]]; PAULI[2] = [[0, -1j], [1j, 0]]; PAULI[3] = [[1, 0], [0, -1]]


def coeff_tensors(p):
    """multi-affine coefficient tensors of Z_cur and Z_next: arrays of shape (4,)*nv, index 0 = constant, 1..3 = x,y,z
    component of slot vector i (radius included)."""
    nv = p.nv
    # site tensors with open slot indices: om[x][state, a1, a2, ...]
    om = {}
    slots_of = {x: [i for i, (y, t) in enumerate(p.vars) if y == x] for x in RING}
    for x in RING:
        t = p.base(x)
        for i in slots_of[x]:
            vec = np.concatenate([np.ones((13, 1)), p.rad[i] * FR], axis=1)       # (13,4)
            t = t[..., None] * vec.reshape((13,) + (1,) * (t.ndim - 1) + (4,))
        om[x] = t
    B = [BOND if b else ONES for b in p.ringbond]
    letters = 'abcdefghijklmnopqrstuvwxyz'
    lab = {}
    k = 0
    for x in RING:
        lab[x] = letters[k:k + len(slots_of[x])]; k += len(slots_of[x])
    order = ''.join(lab[x] for x in RING)          # slot order = order in which ring sites are listed
    perm_vars = [i for x in RING for i in slots_of[x]]
    # ring state indices
    st = dict(zip(RING, 'ABCDEFGH'))

    def contract(ge, gn, gw):
        """sum over states with extra state-weights ge, gn, gw (13,) arrays or Gram couplings handled outside"""
        ops = []; subs = []
        for x in RING:
            ops.append(om[x]); subs.append(st[x] + lab[x])
        for i in range(8):
            ops.append(B[i]); subs.append(st[RING[i]] + st[RING[(i + 1) % 8]])
        return ops, subs
    ops, subs = contract(None, None, None)
    expr = ','.join(subs) + '->' + order
    Z = np.einsum(expr, *ops, optimize='greedy')
    vn = p.vn

    def corr(x, y):
        if not (x in vn and y in vn):
            return np.zeros_like(Z)
        e2 = ','.join(subs) + ',' + st[x] + st[y] + '->' + order
        return np.einsum(e2, *ops, GR, optimize='greedy')
    CeN, CeW, CNW = corr(E, N), corr(E, W), corr(N, W)
    cur = Z + (CeN + CeW + CNW) / 3
    if len(p.fg) == 2:
        cfg = {frozenset((E, N)): CeN, frozenset((E, W)): CeW, frozenset((N, W)): CNW}[frozenset(p.fg)]
    else:
        cfg = 0.0
    nxt = Z + cfg / 5
    # reorder axes to the order of p.vars
    inv = np.argsort(perm_vars)
    return np.transpose(cur, inv), np.transpose(nxt, inv)


def to_operator(f, Sset=()):
    """operator sum_alpha f_alpha sigma^alpha as a 2^n x 2^n matrix; qubits in Sset are transposed."""
    n = f.ndim
    T = f.astype(complex)
    for k in range(n):
        Pk = PAULI.transpose(0, 2, 1) if k in Sset else PAULI
        T = np.tensordot(T, Pk, axes=([0], [0]))       # axis k consumed, appended (i_k, j_k) at the end
    # axes now: i_1,j_1,i_2,j_2,...
    T = T.transpose(list(range(0, 2 * n, 2)) + list(range(1, 2 * n, 2))).reshape(2 ** n, 2 ** n)
    return T


def evalF(f, U):
    t = f
    for u in U:
        t = np.tensordot(np.concatenate([[1.0], u]), t, axes=([0], [0]))
    return float(t)


def gen_min_eig(A, Bm, tol=1e-9):
    """min generalised eigenvalue of (A, B) on the range of B (B PSD)."""
    w, V = np.linalg.eigh(Bm)
    keep = w > tol * w.max()
    Vk = V[:, keep] / np.sqrt(w[keep])
    Ar = Vk.conj().T @ A @ Vk
    ev = np.linalg.eigvalsh((Ar + Ar.conj().T) / 2)
    # also check A is ~0 on the kernel of B
    Vn = V[:, ~keep]
    resid = np.abs(Vn.conj().T @ A @ Vn).max() if Vn.shape[1] else 0.0
    return ev[0], int(keep.sum()), resid


if __name__ == '__main__':
    P = load()
    pid = int(sys.argv[1]) if len(sys.argv) > 1 else 5420
    p = Pattern(P[pid], refined=True)
    val, U = p.minimise(restarts=4, seed=1)
    print('pid', pid, 'out', p.out, 'nv', p.nv, 'classical min', val)
    cur, nxt = coeff_tensors(p)
    print('check coefficient tensor at the minimiser:', evalF(cur, U * p.rad[:, None] / p.rad[:, None]) / evalF(nxt, U), '(radius is inside the tensor)')
    # sign pattern along the principal axis of the minimiser
    w, vecs = np.linalg.eigh(U.T @ U)
    ax = vecs[:, -1]
    sgn = np.sign(U @ ax)
    print('signs along principal axis', sgn, 'collinearity', np.abs(U @ ax).min())
    for name, Sset in (('none', ()), ('minus group', tuple(i for i in range(p.nv) if sgn[i] < 0))):
        A = to_operator(cur, Sset); Bm = to_operator(nxt, Sset)
        print('  S =', name, Sset, 'max imag', np.abs(A.imag).max(), 'herm err', np.abs(A - A.conj().T).max())
        lam, rk, resid = gen_min_eig(A, Bm)
        print('    min generalised eigenvalue %.6f  rank(B) %d  resid on ker %.2e  (lambda_min(B) > 0: %s)' % (lam, rk, resid, np.linalg.eigvalsh(Bm)[0]))
