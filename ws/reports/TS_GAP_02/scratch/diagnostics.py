"""Finite diagnostic calculations only; no Lean proofs or repository writes."""
from dataclasses import dataclass
from fractions import Fraction as F
from itertools import product
from math import prod
import json


@dataclass(frozen=True)
class Q5:
    a: F = F(0)
    b: F = F(0)

    @staticmethod
    def coerce(x):
        return x if isinstance(x, Q5) else Q5(F(x))

    def __add__(self, other):
        other = self.coerce(other)
        return Q5(self.a + other.a, self.b + other.b)

    __radd__ = __add__

    def __neg__(self):
        return Q5(-self.a, -self.b)

    def __sub__(self, other):
        return self + -self.coerce(other)

    def __rsub__(self, other):
        return self.coerce(other) - self

    def __mul__(self, other):
        other = self.coerce(other)
        return Q5(self.a * other.a + 5 * self.b * other.b,
                  self.a * other.b + self.b * other.a)

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = self.coerce(other)
        denominator = other.a**2 - 5 * other.b**2
        assert denominator != 0
        return self * Q5(other.a / denominator, -other.b / denominator)

    def sign(self):
        if not self.b:
            return (self.a > 0) - (self.a < 0)
        if not self.a:
            return (self.b > 0) - (self.b < 0)
        if (self.a > 0) == (self.b > 0):
            return 1 if self.a > 0 else -1
        delta = self.a**2 - 5 * self.b**2
        return ((delta > 0) - (delta < 0)) * (1 if self.a > 0 else -1)

    def __float__(self):
        return float(self.a) + float(self.b) * 5**0.5


def check_frame_constants():
    sqrt5 = Q5(F(0), F(1))
    phi = (1 + sqrt5) / 2
    radius_squared = phi + 2
    bound = (5 - sqrt5) / 505
    assert bound.sign() > 0 and (1 - bound).sign() > 0
    raw = []
    for family, s, t in product(range(3), (1, -1), (1, -1)):
        a, b = Q5(F(s)), t * phi
        raw.append(((Q5(), a, b), (a, b, Q5()), (b, Q5(), a))[family])

    def rotate(v):
        x, y, z = v
        return (F(99, 101) * x - F(20, 101) * y,
                F(20, 101) * x + F(99, 101) * y, z)

    frames = [raw, list(map(rotate, raw))]
    frames.append(list(map(rotate, frames[-1])))
    factors = []
    for i, j in product(range(3), repeat=2):
        if i == j:
            continue
        for u, v in product(frames[i], frames[j]):
            dot = sum((x * y for x, y in zip(u, v)), Q5()) / radius_squared
            for sign in (1, -1):
                factor = 1 + sign * dot
                assert (factor - bound).sign() >= 0
                assert (2 - bound - factor).sign() >= 0
                factors.append(factor)
    assert bound in factors and 2 - bound in factors
    return {"arithmetic": "exact Q(sqrt(5))", "signed_factors": len(factors),
            "frameBound_approx": float(bound), "bounds_attained": True}


def normalized(values):
    mass = sum(values, F(0))
    assert mass > 0
    return [v / mass for v in values]


def restriction(sigma, sites):
    return tuple(sigma[i] for i in sites)


def subsets(n):
    return [tuple(i for i in range(n) if mask & (1 << i)) for mask in range(1 << n)]


def marginal(configs, weights, sites):
    result = {}
    for sigma, weight in zip(configs, weights):
        key = restriction(sigma, sites)
        result[key] = result.get(key, F(0)) + weight
    return result


def maximal(p, q):
    overlap = [min(x, y) for x, y in zip(p, q)]
    t = sum(overlap, F(0))
    result = {(i, i): w for i, w in enumerate(overlap) if w}
    if t < 1:
        for i, x in enumerate(p):
            for j, y in enumerate(q):
                w = (x - overlap[i]) * (y - overlap[j]) / (1 - t)
                if w:
                    result[i, j] = result.get((i, j), F(0)) + w
    return result


def verify_coupling(c, p, q):
    assert all(w >= 0 for w in c.values())
    for i, w in enumerate(p):
        assert sum((v for (a, b), v in c.items() if a == i), F(0)) == w
    for j, w in enumerate(q):
        assert sum((v for (a, b), v in c.items() if b == j), F(0)) == w


def fibre_rows(configs, weights, U):
    outside = tuple(i for i in range(len(configs[0])) if i not in U)
    masses = marginal(configs, weights, outside)
    rows = []
    for sigma in configs:
        key = restriction(sigma, outside)
        rows.append([w / masses[key] if restriction(tau, outside) == key else F(0)
                     for tau, w in zip(configs, weights)])
    return rows


def resample(configs, p, q, c, U, pair_dependent=False):
    P, Q = fibre_rows(configs, p, U), fibre_rows(configs, q, U)
    result = {}
    for (i, j), mass in c.items():
        if pair_dependent and (i + j) % 2:
            row = maximal(P[i], Q[j])
        else:
            row = {(u, v): x * y for u, x in enumerate(P[i]) if x
                   for v, y in enumerate(Q[j]) if y}
        for uv, w in row.items():
            result[uv] = result.get(uv, F(0)) + mass * w
    verify_coupling(result, p, q)
    return result


def norm_sq(z):
    return z[0]**2 + z[1]**2


def subtract(z, w):
    return (z[0] - w[0], z[1] - w[1])


def mean(p, f):
    return tuple(sum((w * z[k] for w, z in zip(p, f)), F(0)) for k in (0, 1))


def variance(p, f):
    m = mean(p, f)
    return sum((w * norm_sq(subtract(z, m)) for w, z in zip(p, f)), F(0))


def squared_error(p, f, h):
    return sum((w * norm_sq(subtract(z, v)) for w, z, v in zip(p, f, h)), F(0))


def check_finite_cases():
    counts = {"shapes": 0, "assignment_inequalities": 0, "patches": 0,
              "pair_dependent_surgeries": 0, "conditional_centerings": 0,
              "product_tensorizations": 0, "normalized_interactions": 0}
    for shape in ((), (1,), (2,), (2, 3), (2, 1, 2), (2, 3, 2)):
        configs = list(product(*(range(s) for s in shape)))
        n, N = len(shape), len(configs)
        p = normalized([F(1 + (3 * k + 2) % 11) for k in range(N)])
        q = normalized([F(1 + (7 * k + 1) % 13) for k in range(N)])
        alpha = min(p + q)
        parts = subsets(n)
        c0 = {(i, j): x * y for i, x in enumerate(p) for j, y in enumerate(q)}
        f = [(F(k * k + 3, 7), F(2 * k - 3, 5)) for k in range(N)]
        v = variance(p, f)
        z = (F(2, 7), F(-3, 5))
        assert squared_error(p, f, [z] * N) == v + norm_sq(subtract(mean(p, f), z))

        for U in parts:
            resample(configs, p, q, c0, U, pair_dependent=True)
            counts["pair_dependent_surgeries"] += 1
            rows = fibre_rows(configs, p, U)
            Ef = [mean(row, f) for row in rows]
            outside = tuple(i for i in range(n) if i not in U)
            h = [(F(1 + sum((i + 1) * (s[i] + 1) for i in outside)),
                  F(2 - sum(s[i] for i in outside))) for s in configs]
            assert squared_error(p, f, h) == squared_error(p, f, Ef) + squared_error(p, Ef, h)
            counts["conditional_centerings"] += 1

            for J in parts:
                if set(U) & set(J):
                    continue
                for weights in (p, q):
                    given = marginal(configs, weights, J)
                    joint_sites = tuple(sorted(U + J))
                    joint = marginal(configs, weights, joint_sites)
                    for key, mass in joint.items():
                        as_map = dict(zip(joint_sites, key))
                        jkey = tuple(as_map[j] for j in J)
                        assert mass / given[jkey] >= alpha**len(U)
                        counts["assignment_inequalities"] += 1

                B = J
                pB, qB = marginal(configs, p, B), marginal(configs, q, B)
                keys = list(pB)
                key_index = {key: k for k, key in enumerate(keys)}
                cB = maximal([pB[key] for key in keys], [qB[key] for key in keys])
                complete = {}
                for i, sigma in enumerate(configs):
                    a = restriction(sigma, B)
                    for j, tau in enumerate(configs):
                        b = restriction(tau, B)
                        mass = cB.get((key_index[a], key_index[b]), F(0))
                        if mass:
                            complete[i, j] = mass * p[i] / pB[a] * q[j] / qB[b]
                verify_coupling(complete, p, q)
                output = resample(configs, p, q, complete, U)
                target = tuple(sorted(U + B))
                success = sum((mass for (i, j), mass in output.items()
                               if restriction(configs[i], target) == restriction(configs[j], target)), F(0))
                t = sum((min(pB[key], qB[key]) for key in keys), F(0))
                assert success >= t * alpha**(2 * len(U))
                counts["patches"] += 1

        sites = [normalized([F(1 + i + a) for a in range(size)])
                 for i, size in enumerate(shape)]
        pi = [prod((sites[i][s[i]] for i in range(n)), start=F(1)) for s in configs]
        assert sum(pi, F(0)) == 1 and all(w > 0 for w in pi)
        D = F(0)
        for x in range(n):
            Ef = [mean(row, f) for row in fibre_rows(configs, pi, (x,))]
            D += squared_error(pi, f, Ef)
        assert variance(pi, f) <= D
        counts["product_tensorizations"] += 1
        psi = [F(1 + k % 5, 3) for k in range(N)]
        lo, hi = min(psi), max(psi)
        Z = sum((w * t for w, t in zip(pi, psi)), F(0))
        mu = [w * t / Z for w, t in zip(pi, psi)]
        assert sum(mu, F(0)) == 1 and all(w > 0 for w in mu)
        assert all(lo / Z * w <= m <= hi / Z * w for w, m in zip(pi, mu))
        counts["normalized_interactions"] += 1
        counts["shapes"] += 1
    return counts


if __name__ == "__main__":
    print(json.dumps({"frame": check_frame_constants(), "finite": check_finite_cases()}, indent=2))
