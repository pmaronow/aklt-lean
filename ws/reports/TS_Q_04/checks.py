"""Exact finite diagnostics for the truth sweep; no Lean proofs are generated."""

from fractions import Fraction as Q
from math import comb
from pathlib import Path
import json


def zeros(m, n):
    return [[Q(0) for _ in range(n)] for _ in range(m)]


def identity(n):
    return [[Q(i == j) for j in range(n)] for i in range(n)]


def mm(a, b):
    return [[sum(x * y for x, y in zip(row, col)) for col in zip(*b)] for row in a]


def rank(a):
    a = [list(map(Q, row)) for row in a]
    r = 0
    for j in range(len(a[0])):
        p = next((i for i in range(r, len(a)) if a[i][j]), None)
        if p is None:
            continue
        a[r], a[p] = a[p], a[r]
        d = a[r][j]
        a[r] = [x / d for x in a[r]]
        for i in range(r + 1, len(a)):
            c = a[i][j]
            a[i] = [x - c * y for x, y in zip(a[i], a[r])]
        r += 1
        if r == len(a):
            break
    return r


def charpoly(a):
    """Coefficients in descending order, by Faddeev--LeVerrier."""
    n = len(a)
    b = identity(n)
    out = [Q(1)]
    for k in range(1, n + 1):
        ab = mm(a, b)
        c = -sum(ab[i][i] for i in range(n)) / k
        out.append(c)
        b = [[ab[i][j] + (c if i == j else 0) for j in range(n)] for i in range(n)]
    return out


def polynomial_from_roots(roots):
    out = [Q(1)]
    for x in roots:
        new = [Q(0)] * (len(out) + 1)
        for i, c in enumerate(out):
            new[i] += c
            new[i + 1] -= x * c
        out = new
    return out


def pair_checks():
    # D[j,k] = sqrt(choose(4,j)*choose(4,k)).  Positivity plus the
    # following squared identities gives D J+ D^-1[j-1,j] = j,
    # and D J- D^-1[j+1,j] = 4-j, without numerical radicals.
    choose = [comb(4, j) for j in range(5)]
    for j in range(1, 5):
        assert Q(choose[j - 1], choose[j]) * j * (5 - j) == j * j
    for j in range(4):
        assert Q(choose[j + 1], choose[j]) * (j + 1) * (4 - j) == (4 - j) ** 2
    assert all(c > 0 for c in choose)

    labels = [(j, k) for j in range(5) for k in range(5)]
    index = {p: i for i, p in enumerate(labels)}
    z, up, down = zeros(25, 25), zeros(25, 25), zeros(25, 25)
    for c, (j, k) in enumerate(labels):
        z[c][c] = 4 - j - k
        for side, q in enumerate((j, k)):
            if q:
                dst = (j - 1, k) if side == 0 else (j, k - 1)
                up[index[dst]][c] = q
            if q < 4:
                dst = (j + 1, k) if side == 0 else (j, k + 1)
                down[index[dst]][c] = 4 - q
    zz, ud, du = mm(z, z), mm(up, down), mm(down, up)
    a = [[zz[i][j] + (ud[i][j] + du[i][j]) / 2 for j in range(25)] for i in range(25)]
    diag = [[Q(j + k == s) for j, k in labels] for s in range(9)]
    assert rank(diag) == 9

    # The adjoint diagonal coefficient vectors w_s have entries
    # sqrt(choose(4,j)*choose(4,k)) for j+k=s. D w_s has integer entries.
    vectors = []
    for s in range(9):
        v = [Q(choose[j] * choose[k] if j + k == s else 0) for j, k in labels]
        av = [sum(x * y for x, y in zip(row, v)) for row in a]
        assert av == [20 * x for x in v]
        vectors.append(v)
    assert rank(vectors) == 9

    blocks = []
    for s in range(9):
        ix = [i for i, (j, k) in enumerate(labels) if j + k == s]
        assert all(a[i][j] == 0 for i in ix for j in range(25) if j not in ix)
        block = [[a[i][j] for j in ix] for i in ix]
        shifted = [[x - (20 if i == j else 0) for j, x in enumerate(row)] for i, row in enumerate(block)]
        r = rank(shifted)
        assert len(ix) - r == 1
        spectrum = [ell * (ell + 1) for ell in range(abs(4 - s), 5)]
        cp = charpoly(block)
        assert cp == polynomial_from_roots(spectrum)
        blocks.append({"j_plus_k": s, "size": len(ix), "rank_C_minus_20I": r,
                       "nullity": len(ix) - r, "eigenvalues": spectrum,
                       "charpoly_descending": [int(c) for c in cp]})
    return {"method": "exact Fraction arithmetic after positive diagonal similarity D C D^-1",
            "binomial_coefficients": choose, "pair_dimension": 25,
            "diagonal_rank": 9, "diagonal_kernel_dimension": 16,
            "independent_top_vectors_checked": len(vectors),
            "eigenvalue_20_dimension": sum(b["nullity"] for b in blocks), "blocks": blocks}


def geometry_checks():
    cases = []
    for l in range(3, 9):
        for n in range(3, 9):
            sites = [(i, j) for i in range(l) for j in range(n)]
            bonds = [(x, d) for x in sites for d in range(2)]
            endpoints, determinants = [], []
            counts = {x: 0 for x in sites}
            for x, d in bonds:
                y = ((x[0] + 1) % l, x[1]) if d == 0 else (x[0], (x[1] + 1) % n)
                assert x != y
                assert len({(x, 0), (x, 1), (y, 0), (y, 1)}) == 4
                endpoints.append(frozenset((x, y)))
                # Two monomials with coefficients +1 and -1, modulo overall sign.
                determinants.append(frozenset((tuple(sorted(((x, 0), (y, 1)))),
                                               tuple(sorted(((x, 1), (y, 0)))))))
                counts[x] += 1
                counts[y] += 1
            assert len(set(endpoints)) == len(bonds)
            assert len(set(determinants)) == len(bonds)
            assert set(counts.values()) == {4}
            cases.append({"L": l, "N": n, "bonds": len(bonds)})
    return {"cases_checked": len(cases), "period_range_inclusive": [3, 8],
            "checks": ["no loops", "no repeated unordered endpoints",
                       "four distinct endpoint spinor variables", "four incident bonds per site",
                       "distinct determinant polynomials up to a nonzero scalar"], "cases": cases}


if __name__ == "__main__":
    result = {"pair": pair_checks(), "geometry": geometry_checks()}
    Path(__file__).with_name("checks.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"pair": {k: v for k, v in result["pair"].items() if k != "blocks"},
                      "weight_block_nullities": [b["nullity"] for b in result["pair"]["blocks"]],
                      "torus_cases_checked": result["geometry"]["cases_checked"]}, indent=2))
