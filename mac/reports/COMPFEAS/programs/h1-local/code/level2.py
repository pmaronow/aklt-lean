"""Float pilot: the inversion (operator) certificate on the GENERIC level-2 patch (radius-3 diamond), agent 70 NOTES 9.

Geometry (agents 60/67): v = (0,0) removed after integration; the trail came straight up, (0,-1), (0,-2), (0,-3) passed
once, everything else unvisited.  Boundary: the 8 ring sites r0..r7 = (2,1),(1,2),(-1,2),(-2,1),(-2,-1),(-1,-2),(1,-2),
(2,-1) (two slots each -> spin 1) and the far tips (3,0),(0,3),(-3,0) (three slots -> one vector of radius 3/5).
In this pilot the three far-tip vectors are FIXED to +-(3/5) e_z (argument), so the operator acts on 8 spins 1
(dimension 6561) and conserves S^z; the smallest generalised eigenvalue over all S^z sectors is a lower bound for the
infimum over the 16 ring slots at these far-tip values.  Minimising over the 8 sign choices of the far tips gives the
collinear-far-tip value to compare with agent 67's level-2 minima (turn 1.019957, straight 1.054036).

Usage: level2.py turn|straight [S as string of 8 chars +/- for r0..r7]"""
import sys, itertools, time
import numpy as np
sys.path.insert(0, '/home/user/otis-claude/research/aklt-gap/agents/70-local-bounds/code')
from cert import mtensor, PAULI, BSYM

M4 = mtensor(4, 'u')[0] / mtensor(4, 'u')[1]
M2d = mtensor(2, 'd')[0] / mtensor(2, 'd')[1]
# spin-1 operator basis of a slot pair: SIG2[al, be, t, t'] = B^T (sigma^al x sigma^be) B
SIG2 = np.zeros((4, 4, 3, 3), complex)
for a in range(4):
    for b in range(4):
        SIG2[a, b] = BSYM.T @ np.kron(PAULI[a], PAULI[b]) @ BSYM
SGN = np.array([1.0, -1.0, -1.0, -1.0])
TW = np.array([2, 0, -2])                      # 2 S^z of the spin-1 basis states


def ring_op(inv):
    """operator-valued tensor of a ring site: [bond, bond', t, t']"""
    T = M4 * (SGN[None, None, :, None] * SGN[None, None, None, :] if inv else 1.0)
    return np.einsum('abxy,xytu->abtu', T, SIG2)


def halves(out, S, far):
    O = [ring_op(s) for s in S]
    phi = lambda sg: np.array([1.0, 0.0, 0.0, 0.6 * sg])
    Te = np.einsum('xyzf,f->xyz', M4, phi(far[0]))
    TNt = np.einsum('xyzf,f->xyz', M4, phi(far[1]))
    TWt = np.einsum('xyzf,f->xyz', M4, phi(far[2]))
    # East: e[A,x,y,z] te[x,p,q] c0[y,a,i,j] c3[z,c,k,l] r0[p,i,m,M] r1[j,b,n,N] r6[k,d,o,O] r7[q,l,r,R]
    East = np.einsum('Axyz,xpq,yaij,zckl,pimM,jbnN,kdoO,qlrR->AabcdmnorMNOR',
                     M4, Te, M4, M4, O[0], O[1], O[6], O[7], optimize='greedy')
    East = East.reshape(4, 256, 81, 81)
    # West: W[A,x,y,z] tW[x,p,q] c1[y,a,i,j] c2[z,c,k,l]; bonds: a = c1-N, b = r2-tN, c = c2-s, d = r5-ts
    # r2[i,b,m,M] (c1 side i, tN side b), r3[j,p,n,N] (c1 side j, tW side p), r4[q,k,o,O] (tW side q, c2 side k),
    # r5[l,d,r,R] (c2 side l, ts side d)
    West = np.einsum('Axyz,xpq,yaij,zckl,ibmM,jpnN,qkoO,ldrR->AabcdmnorMNOR',
                     M4, TWt, M4, M4, O[2], O[3], O[4], O[5], optimize='greedy')
    West = West.reshape(4, 256, 81, 81)
    # spine: N[A,x,a,a'] tN[x,b,b'] s[c',c] ts[d',d]  -> [A; a,b,c,d (east bonds); a',b',c',d' (west bonds)]
    Sp = np.einsum('Axae,xbf,gc,hd->Aabcdefgh', M4, TNt, M2d, M2d, optimize='greedy').reshape(4, 256, 256)
    return East, West, Sp


def assemble(out, S, far, verbose=False):
    East, West, Sp = halves(out, S, far)
    # combine over the v-leg indices: cur = Z + (C_eN + C_eW + C_NW)/3 ; next = Z + C_fg/5
    ES = np.einsum('Aaij,Bab->ABbij', East, Sp, optimize=True)        # [a_e, a_N, west bonds, E, E']
    X = {}
    # X_cur[a_W][b, E, E'] and X_next[a_W][...]
    Xc0 = ES[0, 0] + (ES[1, 1] + ES[2, 2] + ES[3, 3]) / 3.0
    Xc = [Xc0] + [(ES[k, 0] + ES[0, k]) / 3.0 for k in (1, 2, 3)]
    if out == 'turn':        # out = e, (f, g) = (N, W)
        Xn = [ES[0, 0]] + [ES[0, k] / 5.0 for k in (1, 2, 3)]
    else:                    # out = N, (f, g) = (e, W)
        Xn = [ES[0, 0]] + [ES[k, 0] / 5.0 for k in (1, 2, 3)]
    mE = np.zeros(1, int)
    for _ in range(4):
        mE = (mE[:, None] + TW[None, :]).ravel()
    res = {}
    for M in range(-16, 17, 2):
        rows = [(e, w) for e in range(81) for w in range(81) if mE[e] + mE[w] == M]
        if not rows:
            continue
        er = np.array([r[0] for r in rows]); wr = np.array([r[1] for r in rows])
        n = len(rows)
        A = np.zeros((n, n), complex); B = np.zeros((n, n), complex)
        for k in range(4):
            for b0 in range(0, 256, 8):
                sl = slice(b0, b0 + 8)
                Wk = West[k, sl][:, wr][:, :, wr]
                A += np.einsum('brc,brc->rc', Xc[k][sl][:, er][:, :, er], Wk)
                B += np.einsum('brc,brc->rc', Xn[k][sl][:, er][:, :, er], Wk)
        res[M] = (A, B)
        if verbose:
            print('   sector 2Sz=%d size %d  imag %.1e' % (M, n, max(np.abs(A.imag).max(), np.abs(B.imag).max())), flush=True)
    return res


def c_S(out, S, far, verbose=False):
    res = assemble(out, S, far, verbose)
    best = np.inf; where = None
    for M, (A, B) in res.items():
        A = (A.real + A.real.T) / 2; B = (B.real + B.real.T) / 2
        w, V = np.linalg.eigh(B)
        if w[0] <= 1e-11 * w[-1]:
            return None, M
        Xm = V / np.sqrt(w)
        lam = np.linalg.eigvalsh(Xm.T @ A @ Xm)[0]
        if lam < best:
            best, where = lam, M
    return best, where


if __name__ == '__main__':
    out = sys.argv[1] if len(sys.argv) > 1 else 'turn'
    Sstr = sys.argv[2] if len(sys.argv) > 2 else None
    t0 = time.time()
    # default inversion pattern from the level-1 minimisers: turn: the east group (r7, r0, r6) negative;
    cands = [Sstr] if Sstr else (['-+++++--', '--++++--', '-++++---'] if out == 'turn' else ['-++--++-', '+--++--+', '++----++'])
    for Ss in cands:
        S = tuple(ch == '-' for ch in Ss)
        for far in itertools.product((1, -1), repeat=3):
            lam, where = c_S(out, S, far)
            print(out, 'S', Ss, 'far tips (e,N,W)', far, 'c_S', lam, 'sector', where, 'time %.0fs' % (time.time() - t0), flush=True)
