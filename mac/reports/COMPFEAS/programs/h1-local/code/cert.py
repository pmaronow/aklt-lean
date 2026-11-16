"""Inversion (operator) certificates for the level-1 step inequalities, with exact arithmetic (agent 70, NOTES 4-5).

Pipeline for one pattern (refined slot model, NOTES Entry 2) and one inversion set S:
 1. exact multi-affine coefficient tensors  cur_int = 3 D Z_cur,  next_int = 5 D Z_next  (integers; D = product of the
    denominators of the site moment tensors), by contracting the ring in the Pauli basis with exact moment tensors.
    Arithmetic: float64 holding integers; every intermediate is checked to be < 2^52 in absolute value, and all
    tensors entering the ring contraction are entrywise non-negative, so every float operation is exact.
 2. invert the slots in S (sign of the coefficients with a non-zero index there), pass to the operator
    W = sum_alpha f_alpha sigma^alpha in the z-basis, restrict the two slots of each unvisited corner to the
    symmetric subspace (basis |uu>, |ud>+|du>, |dd>), split into sectors of the total S^z.
 3. float: smallest generalised eigenvalue of (W_cur, W_next) per sector  -> c_S (exploration);
    exact: for c = p/q, positive definiteness of  5 q W_cur_int - 3 p W_next_int  on every sector by fraction-free
    (Bareiss) elimination in Python integers: all leading principal minors positive.
Lemma 4.1 then gives  Z_cur - c Z_next >= 0  for all unit slot vectors."""
import sys, itertools, json, time
from fractions import Fraction as Fr
import numpy as np
sys.path.insert(0, '/home/user/otis-claude/research/aklt-gap/agents/70-local-bounds/code')
from ring import Pattern, load, RING, E, N, W, S, C0, C1, C2, C3, TIP, bk, V, TIPRAD

LIM = float(2 ** 52)


def dfact(n):
    r = 1
    while n > 1:
        r *= n
        n -= 2
    return r


def mom_unif(cols):
    e = [0, 0, 0]
    for c in cols:
        if c:
            e[c - 1] += 1
    if any(k % 2 for k in e):
        return Fr(0)
    return Fr(dfact(e[0] - 1) * dfact(e[1] - 1) * dfact(e[2] - 1), dfact(sum(e) + 1))


_MT = {}


def mtensor(k, kind):
    """(integer-valued float array of shape (4,)*k, lcd) with array/lcd = exact Pauli moment tensor of the site measure."""
    if (k, kind) in _MT:
        return _MT[(k, kind)]
    vals = {}
    for c in itertools.product(range(4), repeat=k):
        m = mom_unif(c)
        if kind == 'd':
            m = Fr(3, 5) * m + (Fr(2, 5) if all(x == 0 for x in c) else Fr(0))
        vals[c] = m
    lcd = 1
    for v in vals.values():
        lcd = lcd * v.denominator // np.gcd(lcd, v.denominator)
    lcd = int(lcd)
    T = np.zeros((4,) * k)
    for c, v in vals.items():
        x = v * lcd
        assert x.denominator == 1 and x >= 0
        T[c] = float(x.numerator)
    _MT[(k, kind)] = (T, lcd)
    return T, lcd


def chk(T):
    assert np.all(np.abs(T) < LIM), 'integer overflow of the exact float range'
    return T


I61 = float(2 ** 61)


def itensordot(A, B, axes):
    """exact tensordot of non-negative int64 arrays: the float shadow (relative error ~1e-13) bounds every entry of
    the result below 2^61; all partial sums are sums of non-negative terms, so no int64 overflow can occur."""
    assert A.dtype == np.int64 and B.dtype == np.int64 and A.min(initial=0) >= 0 and B.min(initial=0) >= 0
    shadow = np.tensordot(A.astype(float), B.astype(float), axes=axes)
    assert shadow.max(initial=0.0) < I61, 'int64 overflow'
    return np.tensordot(A, B, axes=axes)


class Net:
    """exact Pauli-basis network of a pattern.  Slot order: ring order e, c0, N, c1, W, c2, s, c3 (tips first on d1).
    leafred: a corner with one present bond is replaced by one slot of radius rho (exact leaf reduction)."""

    def __init__(self, p, leafred=True):
        self.p = p
        self.leafred = leafred
        self.slots = []            # (site, 'tip'|'slot')
        self.site_slots = {}
        self.leaf = {}             # leaf corners: site -> (a, b) with radius a/b
        for i, x in enumerate(RING):
            ns = (1 if (x in TIP and bk(x, TIP[x]) in p.present) else 0) if x in TIP else p.nslot[x]
            if leafred and x not in TIP and ns > 0 and int(p.ringbond[i - 1]) + int(p.ringbond[i]) == 1:
                # corner with one present bond = pendant site: acts through a field of radius rho_kind(1,..,1)
                rad = {('u', 2): (1, 2), ('d', 2): (1, 3), ('d', 1): (1, 5), ('u', 1): (1, 3)}[(p.kind[x], ns)]
                self.leaf[x] = rad
                ns = 1
            self.site_slots[x] = list(range(len(self.slots), len(self.slots) + ns))
            self.slots += [(x, 'tip' if x in TIP else ('leaf' if x in self.leaf else 'slot'))] * ns
        self.n = len(self.slots)
        self.scale = 1             # D
        self.T = {}
        for i, x in enumerate(RING):
            L = p.ringbond[i - 1]; R = p.ringbond[i]
            vleg = x in p.vn
            ns = len(self.site_slots[x])
            if not (p.live[x] or vleg):
                self.T[x] = np.ones((1, 1, 1), dtype=np.int64)
                assert ns == 0
                continue
            if x in self.leaf:
                a, b = self.leaf[x]
                M = np.diag([b, a, a, a]).astype(np.int64).reshape((4, 1, 1, 4) if L else (1, 4, 1, 4))
                self.scale *= b
                self.T[x] = M
                continue
            k = int(L) + int(R) + int(vleg) + ns
            M, lcd = mtensor(k, p.kind.get(x, 'u'))
            self.scale *= lcd
            # axes of M: [L][R][v] slots ; insert singleton axes for absent legs
            sh = [4 if L else 1, 4 if R else 1, 4 if vleg else 1] + [4] * ns
            M = np.rint(M).astype(np.int64).reshape(sh)
            if x in TIP and ns == 1:           # tip slot: vector (b, a u)/b with radius a/b (3/5, or 37/65 at level 1+)
                ta, tb = TIPRAD.numerator, TIPRAD.denominator
                M = M * np.array([tb, ta, ta, ta], dtype=np.int64)
                self.scale *= tb
            self.T[x] = M

    def half(self, sites, vidx):
        """contract consecutive ring sites; returns array [L_first, R_last, slots...] with the v-legs fixed to vidx."""
        A = None
        for x in sites:
            t = self.T[x]
            a = vidx.get(x, 0)
            t = t[:, :, a] if t.shape[2] > 1 else t[:, :, 0]
            if t.shape[2 - 1] == 0:
                pass
            if A is None:
                A = t
            else:
                # A: [L, R, slots...] ; t: [L', R', slots'...] ; contract R with L' (dims equal by construction)
                assert A.shape[1] == t.shape[0]
                A = itensordot(A, t, axes=([1], [0]))            # [L, slotsA..., R', slots'...]
                nA = A.ndim - t.ndim + 1                           # number of axes from A (L + slotsA)
                A = np.moveaxis(A, nA, 1)                          # [L, R', slotsA..., slots'...]
        return A

    def ring(self, vidx):
        h1 = self.half([E, C0, N, C1], vidx)
        h2 = self.half([W, C2, S, C3], vidx)
        s1 = h1.shape[2:]; s2 = h2.shape[2:]
        a = h1.reshape(h1.shape[0], h1.shape[1], -1)               # [l, r, S1]
        b = h2.reshape(h2.shape[0], h2.shape[1], -1)               # [r, l, S2]
        assert a.shape[1] == b.shape[0] and b.shape[1] == a.shape[0]
        F = itensordot(a, b, axes=([0, 1], [1, 0]))                # [S1, S2]
        return F.reshape(s1 + s2)

    def cur_next_int(self):
        """integer tensors 3 D Z_cur and 5 D Z_next (shape (4,)*n, slot order self.slots)."""
        p = self.p
        Z = self.ring({})
        C = {}
        for x, y in ((E, N), (E, W), (N, W)):
            if x in p.vn and y in p.vn:
                C[frozenset((x, y))] = sum(self.ring({x: k, y: k}) for k in (1, 2, 3))      # each term < 2^61 >= 0
        cur = 3 * Z + sum(C.values())
        nxt = 5 * Z + (C[frozenset(p.fg)] if len(p.fg) == 2 else 0)
        # all terms are non-negative int64 below 2^61 individually; bound the sums through the float shadow
        fs = 3 * Z.astype(float) + sum(c.astype(float) for c in C.values())
        assert fs.max(initial=0.0) < I61 / 8 and 5 * Z.astype(float).max(initial=0.0) + fs.max(initial=0.0) < I61 / 8
        assert cur.dtype == np.int64 and nxt.dtype == np.int64
        return cur, nxt


PAULI = np.zeros((4, 2, 2), complex)
PAULI[0] = np.eye(2); PAULI[1] = [[0, 1], [1, 0]]; PAULI[2] = [[0, -1j], [1j, 0]]; PAULI[3] = [[1, 0], [0, -1]]
BSYM = np.array([[1, 0, 0], [0, 1, 0], [0, 1, 0], [0, 0, 1]], float)      # (i1 i2) -> spin-1 basis (unnormalised)
BFULL = np.array([[1, 0, 0, 0], [0, 1, 0, 1], [0, 1, 0, -1], [0, 0, 1, 0]], float)   # + antisymmetric vector
ASYM = np.array([0, 1, -1, 0], float)


def operator_sym_float(net, f, Sset):
    """operator of f o iota_S on prod(tips: C^2) x prod(2-slot corners: Sym^2 C^2).
    Returns (matrix, twoSz of the basis states, exactness flags)."""
    n = net.n
    sign = np.ones((4,) * n)
    for i in Sset:
        sh = [1] * n; sh[i] = 4
        sign = sign * np.array([1.0, -1.0, -1.0, -1.0]).reshape(sh)
    T = (f * sign).astype(complex)
    # groups: list of slot-index tuples (single qubit, or the two slots of a corner)
    groups = []
    for x in RING:
        idx = net.site_slots[x]
        if len(idx) == 2:
            assert (idx[0] in Sset) == (idx[1] in Sset), 'both slots of a corner must be inverted together'
            groups.append(tuple(idx))
        else:
            groups += [(i,) for i in idx]
    # process slot axes in order; consumed axis 0 each time, new axes appended
    asym_resid = 0.0
    dims = []
    twosz = []
    parity = []
    for g in groups:
        if len(g) == 1:
            T = np.tensordot(T, PAULI, axes=([0], [0]))              # (..., i, j)
            dims.append(2); twosz.append(np.array([1, -1])); parity.append(np.array([0, 0]))
        else:
            T = np.tensordot(T, PAULI, axes=([0], [0]))              # slot 1 -> (i1, j1)
            T = np.tensordot(T, PAULI, axes=([0], [0]))              # slot 2 -> (i2, j2); axes (..., i1, j1, i2, j2)
            T = np.moveaxis(T, -3, -2)                               # (..., i1, i2, j1, j2)
            sh = T.shape[:-4]
            T = T.reshape(sh + (4, 4))
            if net.p.kind[net.slots[g[0]][0]] == 'u':
                # unvisited corner: (1 +- n.sigma)^{x2} is supported on the symmetric subspace; the restriction is
                # exact iff the antisymmetric vector is in the kernel on both sides (asserted by the caller)
                asym_resid = max(asym_resid, np.abs(np.tensordot(T, ASYM, axes=([-1], [0]))).max(),
                                 np.abs(np.tensordot(T, ASYM, axes=([-2], [0]))).max())
                T = np.tensordot(T, BSYM, axes=([-2], [0]))          # (..., j, t)
                T = np.tensordot(T, BSYM, axes=([-2], [0]))          # (..., t, t')
                dims.append(3); twosz.append(np.array([2, 0, -2]))
                parity.append(np.array([0, 0, 0]))
            else:
                # diluted corner with two slots (covered model): the delta_0 part acts as the identity, so the
                # antisymmetric vector is not in the kernel.  Basis |uu>, |ud>+|du>, |dd>, |ud>-|du> (congruence by
                # an invertible integer matrix); W commutes with the exchange of the two slots, so the symmetric and
                # antisymmetric parts decouple (checked exactly in Certificate.exact).
                T = np.tensordot(T, BFULL, axes=([-2], [0]))
                T = np.tensordot(T, BFULL, axes=([-2], [0]))
                dims.append(4); twosz.append(np.array([2, 0, -2, 0])); parity.append(np.array([0, 0, 0, 1]))
        assert np.all(np.abs(T.real) < LIM) and np.all(np.abs(T.imag) < LIM)
    k = len(groups)
    T = T.transpose(list(range(0, 2 * k, 2)) + list(range(1, 2 * k, 2)))
    D = int(np.prod(dims))
    Wm = T.reshape(D, D)
    imag = np.abs(Wm.imag).max() if D else 0.0
    q = np.zeros(1, int)
    par = np.zeros(1, int)
    for t, pr in zip(twosz, parity):
        q = (q[:, None] + t[None, :]).ravel()
        par = (2 * par[:, None] + pr[None, :]).ravel()
    q = q + 1000 * par              # sector label: 2 S^z + 1000 * (exchange-parity pattern of the diluted corners)
    return Wm.real.copy(), q, dict(asym=float(asym_resid), imag=float(imag), symm=float(np.abs(Wm.real - Wm.real.T).max()))


I62 = 2 ** 61
BSYM_I = BSYM.astype(np.int64)
BFULL_I = BFULL.astype(np.int64)


def _qubit(Re, Im):
    """axis 0 (Pauli index) -> two trailing axes (i, j): [[f0 + fz, fx - i fy], [fx + i fy, f0 - fz]] in int64."""
    if Re.dtype != object:         # int64: no overflow in the sums below; object dtype = Python integers, unbounded
        assert max(np.abs(Re).max(initial=0), np.abs(Im).max(initial=0)) < I62
    r00 = Re[0] + Re[3]; i00 = Im[0] + Im[3]
    r11 = Re[0] - Re[3]; i11 = Im[0] - Im[3]
    r01 = Re[1] + Im[2]; i01 = Im[1] - Re[2]
    r10 = Re[1] - Im[2]; i10 = Im[1] + Re[2]
    R = np.stack([np.stack([r00, r01], axis=-1), np.stack([r10, r11], axis=-1)], axis=-2)
    I = np.stack([np.stack([i00, i01], axis=-1), np.stack([i10, i11], axis=-1)], axis=-2)
    return R, I


def operator_sym(net, f, Sset):
    """int64 arithmetic; if a magnitude bound fails, the same computation in Python integers (object arrays)."""
    try:
        return _operator_sym(net, f, Sset, np.int64)
    except AssertionError as e:
        if 'both slots' in str(e):
            raise
        return _operator_sym(net, f, Sset, object)


def _operator_sym(net, f, Sset, dtype):
    """operator of f o iota_S on prod(tips, leaf corners: C^2) x prod(2-slot corners: Sym^2 C^2 or C^2 x C^2), in exact
    integer arithmetic (additions only; for int64 the magnitudes are asserted < 2^61 before every step).
    Returns (integer matrix, sector labels, exactness flags)."""
    n = net.n
    assert f.dtype == np.int64
    Re = f.astype(dtype)
    BS = BSYM_I.astype(dtype); BF = BFULL_I.astype(dtype); AS = ASYM.astype(np.int64).astype(dtype)
    for i in Sset:
        sh = [1] * n; sh[i] = 4
        Re = Re * np.array([1, -1, -1, -1], dtype=np.int64).astype(dtype).reshape(sh)
    Im = Re * 0
    groups = []
    for x in RING:
        idx = net.site_slots[x]
        if len(idx) == 2:
            assert (idx[0] in Sset) == (idx[1] in Sset), 'both slots of a corner must be inverted together'
            groups.append(tuple(idx))
        else:
            groups += [(i,) for i in idx]
    asym = 0
    dims = []; twosz = []; parity = []
    for g in groups:
        if len(g) == 1:
            Re, Im = _qubit(Re, Im)
            dims.append(2); twosz.append(np.array([1, -1])); parity.append(np.array([0, 0]))
        else:
            Re, Im = _qubit(Re, Im)                          # slot 1 -> (..., i1, j1)
            Re, Im = _qubit(Re, Im)                          # slot 2 -> (..., i1, j1, i2, j2)
            out = []
            for T in (Re, Im):
                T = np.moveaxis(T, -3, -2)                   # (..., i1, i2, j1, j2)
                T = T.reshape(T.shape[:-4] + (4, 4))
                if dtype != object:
                    assert np.abs(T).max(initial=0) < I62 // 8
                if net.p.kind[net.slots[g[0]][0]] == 'u':
                    asym = max(asym, int(np.abs(np.tensordot(T, AS, axes=([-1], [0]))).max(initial=0)),
                               int(np.abs(np.tensordot(T, AS, axes=([-2], [0]))).max(initial=0)))
                    T = np.tensordot(T, BS, axes=([-2], [0]))
                    T = np.tensordot(T, BS, axes=([-2], [0]))
                else:
                    T = np.tensordot(T, BF, axes=([-2], [0]))
                    T = np.tensordot(T, BF, axes=([-2], [0]))
                out.append(T)
            Re, Im = out
            if net.p.kind[net.slots[g[0]][0]] == 'u':
                dims.append(3); twosz.append(np.array([2, 0, -2])); parity.append(np.array([0, 0, 0]))
            else:
                dims.append(4); twosz.append(np.array([2, 0, -2, 0])); parity.append(np.array([0, 0, 0, 1]))
    k = len(groups)
    perm = list(range(0, 2 * k, 2)) + list(range(1, 2 * k, 2))
    D = int(np.prod(dims)) if dims else 1
    Wm = Re.transpose(perm).reshape(D, D)
    imag = int(np.abs(Im).max(initial=0))
    q = np.zeros(1, int); par = np.zeros(1, int)
    for t, pr in zip(twosz, parity):
        q = (q[:, None] + t[None, :]).ravel()
        par = (2 * par[:, None] + pr[None, :]).ravel()
    q = q + 1000 * par
    return Wm, q, dict(asym=float(asym), imag=float(imag), symm=float(np.abs(Wm - Wm.T).max(initial=0)))


def sector_list(q, least_only):
    labels = sorted(set(q.tolist()))
    if not least_only:
        return labels
    out = []
    for par in sorted(set((l + 500) // 1000 for l in labels)):
        cls = [l for l in labels if (l + 500) // 1000 == par]
        out.append(min(cls, key=lambda l: (abs(l - 1000 * par), -(l - 1000 * par))))
    return out


def sector_min_geneig(A, B):
    w, Vv = np.linalg.eigh(B)
    if w[0] <= 1e-12 * w[-1]:
        return None, w[0] / w[-1]
    X = Vv / np.sqrt(w)
    M = X.T @ A @ X
    return np.linalg.eigvalsh((M + M.T) / 2)[0], w[0] / w[-1]


def bareiss_pd(M):
    """exact test of positive definiteness of a symmetric integer matrix (list of lists of Python ints):
    fraction-free (Bareiss) elimination on Python integers; after step k the entry (i, j), i, j > k, is the minor of
    rows/columns {0..k, i} x {0..k, j} (exact divisions), so the pivots are the leading principal minors.
    Only the upper triangle is updated (the matrix stays symmetric).  Returns (True, None) iff all pivots are > 0."""
    n = len(M)
    A = [list(row) for row in M]
    prev = 1
    for k in range(n):
        Ak = A[k]
        piv = Ak[k]
        if piv <= 0:
            return False, k
        for i in range(k + 1, n):
            aik = Ak[i]                      # = A[i][k] by symmetry (upper triangle is kept up to date)
            Ai = A[i]
            if aik:
                for j in range(i, n):
                    Ai[j] = (Ai[j] * piv - aik * Ak[j]) // prev
            else:
                for j in range(i, n):
                    Ai[j] = (Ai[j] * piv) // prev
        prev = piv
    return True, None


class Certificate:
    def __init__(self, r, refined=True, leafred=True):
        self.refined = refined
        self.p = Pattern(r, refined=refined)
        self.net = Net(self.p, leafred=leafred)
        self.cur, self.nxt = self.net.cur_next_int()
        self.n = self.net.n

    def evaluate(self, U):
        """ratio at unit vectors U (n,3) in net slot order, from the integer tensors (float)."""
        a, b = self.cur.astype(float), self.nxt.astype(float)
        for u in U:
            vec = np.concatenate([[1.0], u])
            a = np.tensordot(vec, a, axes=([0], [0])); b = np.tensordot(vec, b, axes=([0], [0]))
        return (float(a) / 3) / (float(b) / 5)

    def operators(self, Sset):
        key = tuple(sorted(Sset))
        if getattr(self, '_opkey', None) != key:
            A, q, fa = operator_sym(self.net, self.cur, key)
            B, q2, fb = operator_sym(self.net, self.nxt, key)
            flags = {k: max(fa[k], fb[k]) for k in fa}
            self._opkey = key; self._op = (A, B, q, flags)
        return self._op

    def c_S(self, Sset, all_sectors=False):
        """float: smallest generalised eigenvalue of (W_cur/3, W_next/5) over the S^z sectors (default: the sector of
        smallest |S^z| only, which contains every multiplet)."""
        A, B, q, flags = self.operators(Sset)
        best = None
        for s in sector_list(q, not all_sectors):
            idx = np.where(q == s)[0]
            lam, cond = sector_min_geneig(A[np.ix_(idx, idx)].astype(float) / 3, B[np.ix_(idx, idx)].astype(float) / 5)
            if lam is None:
                return None, flags
            best = lam if best is None else min(best, lam)
        return best, flags

    def exact(self, Sset, p_, q_, verbose=False, least_only=False):
        """exact certificate of  Z_cur - (p_/q_) Z_next >= 0: positive definiteness of 5 q W_cur_int - 3 p W_next_int
        on every S^z sector of the symmetric subspace.  Returns dict with status and sizes."""
        A, B, q, flags = self.operators(Sset)
        ok = flags['asym'] == 0.0 and flags['imag'] == 0.0 and flags['symm'] == 0.0
        res = dict(flags=flags, sectors=[], ok=ok)
        if not ok:
            return res
        t0 = time.time()
        # exact block structure: no matrix element between different sectors (S^z, exchange parities)
        diff = q[:, None] != q[None, :]
        if any(x != 0 for x in A[diff].tolist()) or any(x != 0 for x in B[diff].tolist()):
            res['ok'] = False; res['flags']['block'] = 1.0
            return res
        # Lemma 6.1: W commutes with the total spin, so within each exchange-parity class every eigenvalue occurs
        # in the sector of least |S^z|
        for s in sector_list(q, least_only):
            idx = np.where(q == s)[0]
            a = A[np.ix_(idx, idx)]; b = B[np.ix_(idx, idx)]
            assert a.dtype in (np.int64, object) and b.dtype in (np.int64, object)
            M = [[5 * q_ * int(a[i, j]) - 3 * p_ * int(b[i, j]) for j in range(len(idx))] for i in range(len(idx))]
            pd, where = bareiss_pd(M)
            res['sectors'].append((int(s), len(idx), bool(pd)))
            if verbose:
                print('    sector 2Sz=%d size %d PD %s (%.1fs)' % (s, len(idx), pd, time.time() - t0), flush=True)
            if not pd:
                res['ok'] = False
        return res


def ring_to_net(cert, U):
    """ring-engine vectors (p.vars order) -> one vector per net slot (leaf corners: normalised sum of their slots)."""
    p = cert.p
    by_site = {}
    for i, (y, t) in enumerate(p.vars):
        by_site.setdefault(y, []).append(U[i])
    Un = np.zeros((cert.n, 3))
    for x in RING:
        idx = cert.net.site_slots[x]
        if not idx:
            continue
        vs = by_site[x]
        if len(idx) == len(vs):
            for i, v in zip(idx, vs):
                Un[i] = v
        else:                                  # leaf corner: one net slot for several ring slots
            s = np.sum(vs, axis=0)
            Un[idx[0]] = s / max(np.linalg.norm(s), 1e-300)
    return Un


def net_to_ring(cert, Un):
    p = cert.p
    U = np.zeros((p.nv, 3))
    pos = {x: 0 for x in RING}
    for i, (y, t) in enumerate(p.vars):
        idx = cert.net.site_slots[y]
        U[i] = Un[idx[min(pos[y], len(idx) - 1)]]
        pos[y] += 1
    return U


def minus_group(cert, restarts=3, seed=1, sweeps=400, tol=1e-13):
    """numerical minimiser (ring engine); S = the sites whose slots have negative total component along the principal
    axis of the minimiser (all slots of a site are inverted together)."""
    p = cert.p
    val, U = p.minimise(restarts=restarts, seed=seed, sweeps=sweeps, tol=tol)
    if cert.n == 0:
        return val, np.zeros((0, 3)), ()
    Un = ring_to_net(cert, U)
    w, vecs = np.linalg.eigh(Un.T @ Un)
    proj = Un @ vecs[:, -1]
    Sset = []
    for x in RING:
        idx = cert.net.site_slots[x]
        if idx and sum(proj[i] for i in idx) < 0:
            Sset += idx
    return val, Un, tuple(Sset)


if __name__ == '__main__':
    P = load()
    pid = int(sys.argv[1]) if len(sys.argv) > 1 else 5420
    t0 = time.time()
    c = Certificate(P[pid])
    print('pid', pid, 'out', c.p.out, 'slots', c.n, 'scale D =', c.net.scale, 'max |cur_int| %.3e' % np.abs(c.cur).max(),
          'tensors in %.1fs' % (time.time() - t0), flush=True)
    val, Un, Sset = minus_group(c)
    print('  classical minimum (float)', val, ' from integer tensors', c.evaluate(Un), ' S =', Sset, flush=True)
    lam, flags = c.c_S(Sset)
    print('  c_S (float, sector of least |Sz|) = %.9f' % lam, flags, flush=True)
    lam2, _ = c.c_S(Sset, all_sectors=True)
    print('  c_S (float, all sectors)          = %.9f' % lam2, flush=True)
    if len(sys.argv) > 3:
        p_, q_ = int(sys.argv[2]), int(sys.argv[3])
        t0 = time.time()
        res = c.exact(Sset, p_, q_, verbose=True)
        print('  EXACT certificate for c = %d/%d:' % (p_, q_), 'CERTIFIED' if res['ok'] else 'FAILED', res['flags'],
              'time %.1fs' % (time.time() - t0))
