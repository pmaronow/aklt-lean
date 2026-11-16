"""Unit test of cert.bareiss_pd: pivots = leading principal minors (compared with exact Fraction determinants) and
the PD verdict (compared with Sylvester's criterion evaluated in Fractions), on random symmetric integer matrices."""
import sys, random
from fractions import Fraction as Fr
sys.path.insert(0, '/home/user/otis-claude/research/aklt-gap/agents/70-local-bounds/code')
from cert import bareiss_pd


def det(M):
    n = len(M)
    A = [[Fr(x) for x in row] for row in M]
    d = Fr(1)
    for k in range(n):
        p = next((i for i in range(k, n) if A[i][k] != 0), None)
        if p is None:
            return Fr(0)
        if p != k:
            A[k], A[p] = A[p], A[k]; d = -d
        d *= A[k][k]
        for i in range(k + 1, n):
            f = A[i][k] / A[k][k]
            for j in range(k, n):
                A[i][j] -= f * A[k][j]
    return d


random.seed(3)
npd = 0; nnot = 0
for trial in range(400):
    n = random.randint(1, 9)
    X = [[random.randint(-4, 4) for _ in range(n)] for _ in range(n)]
    M = [[sum(X[i][k] * X[j][k] for k in range(n)) - (random.randint(0, 6) if (i == j and trial % 2) else 0) for j in range(n)] for i in range(n)]
    minors = [det([row[:k] for row in M[:k]]) for k in range(1, n + 1)]
    truth = all(m > 0 for m in minors)
    got, where = bareiss_pd(M)
    assert got == truth, (M, minors, got)
    npd += truth; nnot += (not truth)
print('bareiss_pd agrees with Sylvester (exact Fractions) on 400 random matrices:', npd, 'PD,', nnot, 'not PD')
