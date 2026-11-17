"""Finite exact-arithmetic checks of the audited definitions; no Lean proofs."""

from dataclasses import dataclass
from fractions import Fraction as F
from functools import reduce
from itertools import product
from operator import mul
from pathlib import Path
import json
import random


@dataclass(frozen=True)
class Q5:
    a: F = F(0)
    b: F = F(0)

    @staticmethod
    def cast(value):
        return value if isinstance(value, Q5) else Q5(F(value))

    def __add__(self, other):
        other = self.cast(other)
        return Q5(self.a + other.a, self.b + other.b)

    __radd__ = __add__

    def __neg__(self):
        return Q5(-self.a, -self.b)

    def __sub__(self, other):
        return self + -self.cast(other)

    def __rsub__(self, other):
        return self.cast(other) - self

    def __mul__(self, other):
        other = self.cast(other)
        return Q5(self.a * other.a + 5 * self.b * other.b,
                  self.a * other.b + self.b * other.a)

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = self.cast(other)
        denominator = other.a ** 2 - 5 * other.b ** 2
        assert denominator != 0
        return self * Q5(other.a / denominator, -other.b / denominator)

    def __rtruediv__(self, other):
        return self.cast(other) / self

    def __pow__(self, exponent):
        assert isinstance(exponent, int) and exponent >= 0
        return reduce(mul, [self] * exponent, Q5(F(1)))

    def sign(self):
        if self.b == 0:
            return (self.a > 0) - (self.a < 0)
        if self.a == 0:
            return (self.b > 0) - (self.b < 0)
        if self.a > 0 and self.b > 0:
            return 1
        if self.a < 0 and self.b < 0:
            return -1
        difference = self.a ** 2 - 5 * self.b ** 2
        return ((difference > 0) - (difference < 0)) * (1 if self.a > 0 else -1)


def prod(values, start=1):
    return reduce(mul, values, start)


def q5_le(left, right):
    return (Q5.cast(right) - left).sign() >= 0


def frame_checks():
    phi = Q5(F(1, 2), F(1, 2))
    radius_squared = phi + 2
    letters = []
    for axis, sign_a, sign_b in product(range(3), [1, -1], [1, -1]):
        a, b = Q5(F(sign_a)), sign_b * phi
        letters.append([(Q5(), a, b), (a, b, Q5()), (b, Q5(), a)][axis])

    def rotate(v):
        return (F(99, 101) * v[0] - F(20, 101) * v[1],
                F(20, 101) * v[0] + F(99, 101) * v[1], v[2])

    frames = [letters]
    for _ in range(2):
        frames.append([rotate(v) for v in frames[-1]])
    bound = Q5(F(5, 505), F(-1, 505))
    assert bound.sign() > 0 and (1 - bound).sign() > 0
    interactions = {}
    signed_factors = 0
    attained = False
    for i, j in product(range(3), repeat=2):
        for a, b in product(range(12), repeat=2):
            dot = sum(x * y for x, y in zip(frames[i][a], frames[j][b])) / radius_squared
            interactions[i, j, a, b] = 1 + dot
            if i != j:
                for sign in [1, -1]:
                    value = 1 + sign * dot
                    assert q5_le(bound, value) and q5_le(value, 2 - bound)
                    attained = attained or value == bound
                    signed_factors += 1
    assert attained
    return bound, interactions, signed_factors


def plane_checks(bound, interactions):
    shapes = [[], [(0, 0)], [(0, 0), (1, 0)],
              [(0, 0), (2, 0)], [(0, 0), (1, 0), (0, 1)]]
    directions = [(1, 0), (0, 1), (-1, 0), (0, -1)]
    configuration_count = 0
    for colour_count in [2, 3]:
        colour = lambda x: sum(x) % colour_count
        for sites in shapes:
            volume = set(sites)
            internal = [(x, (x[0] + dx, x[1] + dy))
                        for x in sites for dx, dy in directions[:2]
                        if (x[0] + dx, x[1] + dy) in volume]
            legs = [(x, (x[0] + dx, x[1] + dy))
                    for x in sites for dx, dy in directions
                    if (x[0] + dx, x[1] + dy) not in volume]
            exterior = sorted({z for _, z in legs})
            boundary = {z: (3 * i + 7) % 12 for i, z in enumerate(exterior)}
            site_weights = {
                x: [F(1, 12) * prod((interactions[colour(x), colour(z), a, boundary[z]]
                                    for y, z in legs if y == x), Q5(F(1)))
                    for a in range(12)]
                for x in sites
            }
            site_normalizers = {x: sum(weights, Q5()) for x, weights in site_weights.items()}
            assert all(z.sign() > 0 for z in site_normalizers.values())
            data = []
            for values in product(range(12), repeat=len(sites)):
                configuration = dict(zip(sites, values))
                interaction = prod((interactions[colour(x), colour(y), configuration[x], configuration[y]]
                                    for x, y in internal), Q5(F(1)))
                boundary_product = prod((interactions[colour(x), colour(z), configuration[x], boundary[z]]
                                         for x, z in legs), Q5(F(1)))
                raw = F(1, 12) ** len(sites) * interaction * boundary_product
                reference = prod((site_weights[x][configuration[x]] / site_normalizers[x]
                                  for x in sites), Q5(F(1)))
                assert raw.sign() > 0 and reference.sign() > 0
                assert q5_le(bound ** len(internal), interaction)
                assert q5_le(interaction, (2 - bound) ** len(internal))
                data.append((raw, reference, interaction))
            partition = sum((raw for raw, _, _ in data), Q5())
            mean = sum((reference * interaction for _, reference, interaction in data), Q5())
            assert sum((reference for _, reference, _ in data), Q5()) == Q5(F(1))
            assert partition.sign() > 0 and mean.sign() > 0
            lower = bound ** len(internal) / mean
            upper = (2 - bound) ** len(internal) / mean
            assert lower.sign() > 0 and upper.sign() > 0
            assert lower / upper == (bound / (2 - bound)) ** len(internal)
            for raw, reference, interaction in data:
                law = raw / partition
                assert law == reference * interaction / mean
                assert q5_le(lower * reference, law) and q5_le(law, upper * reference)
            configuration_count += len(data)
    return {'volumes_and_boundaries': 2 * len(shapes),
            'configurations': configuration_count,
            'shapes': shapes, 'colour_counts': [2, 3]}


def norm_squared(z):
    return z[0] ** 2 + z[1] ** 2


def subtract(z, w):
    return (z[0] - w[0], z[1] - w[1])


def mean(weights, values, states):
    return tuple(sum(weights[s] * values[s][component] for s in states)
                 for component in range(2))


def variance(weights, values, states):
    centre = mean(weights, values, states)
    return sum(weights[s] * norm_squared(subtract(values[s], centre)) for s in states)


def dirichlet(weights, values, states, site_count):
    energy = F(0)
    for site in range(site_count):
        fibres = {}
        for state in states:
            complement = state[:site] + state[site + 1:]
            fibres.setdefault(complement, []).append(state)
        for fibre in fibres.values():
            mass = sum(weights[state] for state in fibre)
            centre = tuple(c / mass for c in mean(weights, values, fibre))
            energy += sum(weights[state] * norm_squared(subtract(values[state], centre)) for state in fibre)
    return energy


def probability_checks():
    rng = random.Random(8)
    shapes = [[], [1], [2], [2, 1], [2, 3], [2, 2, 2]]
    trials = 0
    product_trials = 0
    zero_variance_checks = 0
    for shape in shapes:
        states = list(product(*(range(size) for size in shape)))
        for _ in range(40):
            weights = []
            for _ in range(2):
                raw = {s: F(rng.randrange(1, 10)) for s in states}
                total = sum(raw.values())
                weights.append({s: raw[s] / total for s in states})
            p, q = weights
            values = {s: (F(rng.randrange(-5, 6)), F(rng.randrange(-5, 6))) for s in states}
            lower = min(q[s] / p[s] for s in states)
            upper = max(q[s] / p[s] for s in states)
            assert variance(q, values, states) <= upper * variance(p, values, states)
            assert lower * dirichlet(p, values, states, len(shape)) <= dirichlet(q, values, states, len(shape))
            assert 0 * dirichlet(p, values, states, len(shape)) <= dirichlet(q, values, states, len(shape))
            trials += 1

            site_laws = []
            for size in shape:
                raw = [F(rng.randrange(1, 10)) for _ in range(size)]
                site_laws.append([value / sum(raw) for value in raw])
            reference = {s: prod(site_laws[x][s[x]] for x in range(len(shape))) for s in states}
            assert sum(reference.values()) == 1
            assert all(weight > 0 for weight in reference.values())
            assert variance(reference, values, states) <= dirichlet(reference, values, states, len(shape))
            product_trials += 1
            constant = {s: (F(2), F(-3)) for s in states}
            assert variance(reference, constant, states) == 0
            assert dirichlet(reference, constant, states, len(shape)) == 0
            zero_variance_checks += 1
            additive = {s: (F(sum((x + 1) * s[x] for x in range(len(shape)))),
                            F(sum(s))) for s in states}
            assert variance(reference, additive, states) == dirichlet(reference, additive, states, len(shape))
    assert not list(product(range(0)))
    return {'density_comparison_trials': trials, 'product_poincare_trials': product_trials,
            'constant_function_trials': zero_variance_checks, 'additive_equality_trials': product_trials,
            'alphabet_sizes': shapes,
            'empty_alphabet_note': 'No probability can normalize on the empty configuration space.'}


if __name__ == '__main__':
    bound, interactions, factor_count = frame_checks()
    print('Exact frame factor bounds checked:', factor_count, flush=True)
    plane_result = plane_checks(bound, interactions)
    print('Exact plane normalization, absorption, density checks:', plane_result, flush=True)
    probability_result = probability_checks()
    print('Exact complex finite probability checks:', probability_result, flush=True)
    result = {'arithmetic': 'Fractions and exact Q(sqrt(5)); no floating-point tolerances',
              'signed_frame_factors_checked': factor_count, 'plane': plane_result,
              'probability': probability_result, 'status': 'PASS'}
    Path(__file__).with_name('checks.json').write_text(json.dumps(result, indent=2) + '\n')
