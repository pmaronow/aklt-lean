"""Exact finite diagnostics for the reviewed definitions; no Lean proofs."""
from fractions import Fraction as F
from itertools import product
from math import floor
import json
from pathlib import Path

counts = {}

# Exhaustive assignment bounds on small positive, nonuniform finite products.
energy_checks = 0
for shape in [(), (1,), (2,), (1, 1), (2, 3, 1), (2, 2, 2)]:
    configs = list(product(*(range(n) for n in shape)))
    for seed in [1, 4]:
        weights = [((k + 1) * (7 * seed + 5) + k * k) % 23 + 1 for k in range(len(configs))]
        p = dict(zip(configs, (F(w, sum(weights)) for w in weights)))
        full_bounds = [F(1)]
        for x in range(len(shape)):
            for sigma in configs:
                fibre = [t for t in configs if all(t[z] == sigma[z] for z in range(len(shape)) if z != x)]
                den = sum(p[t] for t in fibre)
                for letter in range(shape[x]):
                    full_bounds.append(sum(p[t] for t in fibre if t[x] == letter) / den)
        alpha = min(full_bounds)
        assert 0 < alpha <= 1
        for roles in product(range(3), repeat=len(shape)):
            U = [x for x, role in enumerate(roles) if role == 1]
            J = [x for x, role in enumerate(roles) if role == 2]
            for a in configs:
                fibre = [t for t in configs if all(t[x] == a[x] for x in J)]
                den = sum(p[t] for t in fibre)
                assert den > 0
                for b in configs:
                    num = sum(p[t] for t in fibre if all(t[x] == b[x] for x in U))
                    assert alpha ** len(U) <= num / den
                    energy_checks += 1
counts['finite_energy_assignment_inequalities'] = energy_checks

# Actual zero-based Fin h trial indexing, for every empty/singleton exception set.
trial_checks = 0
sharp_examples = []
for h in range(4, 129):
    for exceptions in [set()] + [{e} for e in range(-2, h + 4)]:
        trials = [j for j in range(h) if j + 2 <= h and j + 2 not in exceptions and j + 3 not in exceptions]
        assert h - 3 <= len(trials)
        trial_checks += 1
        if h == 4 and len(trials) == h - 3:
            sharp_examples.append({'h': h, 'exceptions': sorted(exceptions), 'trial_j': trials})
counts['trial_count_cases'] = trial_checks

# Integer floors and strict thresholds, including negative shell indices.
nesting_checks = 0
for s in [F(16), F(65, 4), F(33, 2), F(73, 3)]:
    for i in range(-10, 11):
        for j in range(i + 2, i + 9):
            assert (j - 1) * s >= i * s
            assert floor((j - 1) * s) > i * s
            nesting_checks += 1
counts['nesting_threshold_cases'] = nesting_checks
window_checks = 0
for s in [F(2), F(9, 4), F(4), F(19, 3), F(65, 4)]:
    for i in range(2, floor(s) + 1):
        assert floor(i * s) > (i - 1) * s
        window_checks += 1
counts['window_containment_threshold_cases'] = window_checks

# Conservative propagation of agreement under every skip pattern in short traces.
# Sites represented by integer distances form an abstract finite radial model.
absorption_checks = 0
for s in [F(16), F(65, 4), F(73, 3)]:
    for h in range(2, 8):
        distances = set(range(floor((h + 2) * s) + 2))
        target = {d for d in distances if d > h * s}
        for skip_bits in product([False, True], repeat=h):
            skipped = {i + 2 for i, skip in enumerate(skip_bits) if skip}
            for i in range(2, h + 1):
                if i in skipped or i + 1 in skipped:
                    continue
                agree = {d for d in distances if d == floor(i * s)}
                for k in range(i + 1, h + 2):
                    if k in skipped:
                        continue
                    predecessor = {d for d in distances if d == floor((k - 1) * s)}
                    volume = {d for d in distances if d > (k - 1) * s}
                    if predecessor <= agree:
                        agree = (agree - volume) | volume
                    else:
                        agree -= volume
                assert target <= agree
                absorption_checks += 1
counts['absorption_radial_skip_cases'] = absorption_checks

# Sum nonzero finite traces using pair-dependent couplings of full conditional fibres.
configs = list(product(range(2), repeat=2))
p = dict(zip(configs, [F(1, 10), F(2, 10), F(3, 10), F(4, 10)]))
q = dict(zip(configs, [F(4, 10), F(1, 10), F(2, 10), F(3, 10)]))
pairs = list(product(configs, repeat=2))

def fibre(law, U, sigma):
    admissible = [t for t in configs if all(t[x] == sigma[x] for x in range(2) if x not in U)]
    den = sum(law[t] for t in admissible)
    return {t: law[t] / den if t in admissible else F(0) for t in configs}

def row(j, omega):
    if j == 1:
        return {omega: F(1)}
    U = {0} if j == 0 else {1}
    left = fibre(p, U, omega[0])
    right = fibre(q, U, omega[1])
    if (sum(omega[0]) + sum(omega[1])) % 2 == 0:
        return {(x, y): left[x] * right[y] for x, y in pairs if left[x] * right[y]}
    # Greedy coupling; the ordering and coupling depend on the entire input pair.
    remaining_left = left.copy()
    remaining_right = right.copy()
    result = {}
    for x in configs:
        for y in reversed(configs):
            mass = min(remaining_left[x], remaining_right[y])
            if mass:
                result[x, y] = mass
                remaining_left[x] -= mass
                remaining_right[y] -= mass
    assert all(v == 0 for v in remaining_left.values())
    assert all(v == 0 for v in remaining_right.values())
    return result

trace_checks = 0
support_sizes = []
for h in range(4):
    paths = {(omega,): p[omega[0]] * q[omega[1]] for omega in pairs}
    for j in range(h):
        next_paths = {}
        for t, mass in paths.items():
            transition = row(j, t[-1])
            assert sum(transition.values()) == 1
            assert all(v >= 0 for v in transition.values())
            for omega, weight in transition.items():
                next_paths[t + (omega,)] = mass * weight
        paths = next_paths
    endpoint = {omega: F(0) for omega in pairs}
    for t, mass in paths.items():
        endpoint[t[-1]] += mass
    assert sum(paths.values()) == 1
    for x in configs:
        assert sum(endpoint[x, y] for y in configs) == p[x]
    for y in configs:
        assert sum(endpoint[x, y] for x in configs) == q[y]
    trace_checks += 1
    support_sizes.append(len(paths))
counts['trace_lengths_checked'] = trace_checks
counts['trace_support_sizes_h_0_to_3'] = support_sizes

result = {'status': 'passed', 'counts': counts, 'sharp_trial_examples': sharp_examples,
          'scope': 'Exact finite/rational diagnostics only; these checks do not constitute formal proofs of the leaves.'}
Path(__file__).with_name('diagnostics.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
