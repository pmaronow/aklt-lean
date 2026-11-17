"""Exact finite sanity checks of the audited definitions; no Lean proofs.

Matrices are over Fraction. Quadratic forms are computed from the actual
conditional residual squares, rather than assuming projection identities.
"""

from collections import Counter
from fractions import Fraction as F
from itertools import product
import json
from pathlib import Path
from random import Random


COUNTS = Counter()
RNG = Random(20261116)


def check(condition, label):
    if not condition:
        raise AssertionError(label)
    COUNTS[label] += 1


def states(shape):
    return list(product(*(range(k) for k in shape)))


def normalize(weights):
    total = sum(weights)
    assert total > 0
    return [F(w, total) for w in weights]


def zeros(n):
    return [[F(0) for _ in range(n)] for _ in range(n)]


def combine(n, terms):
    result = zeros(n)
    for coefficient, matrix in terms:
        for i in range(n):
            for j in range(n):
                result[i][j] += coefficient * matrix[i][j]
    return result


def variance_matrix(p):
    return [[(p[i] if i == j else F(0)) - p[i] * p[j]
             for j in range(len(p))] for i in range(len(p))]


def conditional_kernel(omega, p, block):
    outside = set(range(len(omega[0]))) - set(block)
    result = []
    for sigma in omega:
        support = [all(sigma[x] == tau[x] for x in outside) for tau in omega]
        denominator = sum(w for w, keep in zip(p, support) if keep)
        check(denominator > 0, 'positive_fibre_denominator')
        result.append([w / denominator if keep else F(0)
                       for w, keep in zip(p, support)])
    return result


def residual_form(p, kernel):
    n = len(p)
    residual = [[F(i == j) - kernel[i][j] for j in range(n)] for i in range(n)]
    return [[sum(p[k] * residual[k][i] * residual[k][j] for k in range(n))
             for j in range(n)] for i in range(n)]


def block_forms(omega, p):
    nsites = len(omega[0])
    blocks = list(product((False, True), repeat=nsites))
    result = {}
    kernels = {}
    for mask in blocks:
        block = tuple(i for i, included in enumerate(mask) if included)
        kernels[block] = conditional_kernel(omega, p, block)
        result[block] = residual_form(p, kernels[block])
    return result, kernels


def psd(matrix):
    """Exact Schur complement criterion, including singular forms."""
    n = len(matrix)
    if not n:
        return True
    assert all(matrix[i][j] == matrix[j][i] for i in range(n) for j in range(n))
    if any(matrix[i][i] < 0 for i in range(n)):
        return False
    pivot = next((i for i in range(n) if matrix[i][i] > 0), None)
    if pivot is None:
        return all(value == 0 for row in matrix for value in row)
    remaining = [i for i in range(n) if i != pivot]
    schur = [[matrix[i][j] - matrix[i][pivot] * matrix[pivot][j] / matrix[pivot][pivot]
              for j in remaining] for i in remaining]
    return psd(schur)


def stochastic_reversible(p, kernel):
    n = len(p)
    return (all(min(row) >= 0 and sum(row) == 1 for row in kernel)
            and all(p[i] * kernel[i][j] == p[j] * kernel[j][i]
                    for i in range(n) for j in range(n)))


def mean(p, function):
    return sum(w * value for w, value in zip(p, function))


def apply(kernel, function):
    return [mean(row, function) for row in kernel]


def hamming(sigma, tau):
    return sum(a != b for a, b in zip(sigma, tau))


def lipschitz(omega, function):
    return max([F(0)] + [abs(function[i] - function[j])
                        for i, sigma in enumerate(omega)
                        for j, tau in enumerate(omega) if hamming(sigma, tau) == 1])


def quadratic(matrix, function):
    return sum(function[i] * matrix[i][j] * function[j]
               for i in range(len(function)) for j in range(len(function)))


def kernel_form_matrix(p, kernel, scale):
    n = len(p)
    return [[scale * p[i] * (F(i == j) - kernel[i][j])
             for j in range(n)] for i in range(n)]


SHAPES = [(), (1,), (1, 1), (2,), (3,), (2, 2), (1, 3, 2), (2, 2, 2)]

for shape in SHAPES:
    omega = states(shape)
    n = len(omega)
    v = len(shape)
    site_laws = [normalize([RNG.randint(1, 7) for _ in range(k)]) for k in shape]
    reference = []
    for sigma in omega:
        weight = F(1)
        for x in range(v):
            weight *= site_laws[x][sigma[x]]
        reference.append(weight)
    check(sum(reference) == 1, 'product_normalization')
    reference_forms, _ = block_forms(omega, reference)
    reference_dirichlet = combine(n, [(1, reference_forms[(x,)]) for x in range(v)])
    check(psd(combine(n, [(1, reference_dirichlet), (-1, variance_matrix(reference))])),
          'product_tensorization_all_functions')

    # Exhaust the three-valued functions up to six states, sample at eight states.
    functions = (list(product((-1, 0, 1), repeat=n)) if n <= 6
                 else [tuple(RNG.randint(-3, 3) for _ in omega) for _ in range(50)])
    for function in functions:
        lip = lipschitz(omega, function)
        check(lip >= 0 and all(abs(function[i] - function[j]) <= lip * hamming(sigma, tau)
                              for i, sigma in enumerate(omega)
                              for j, tau in enumerate(omega))
              and ((lip == 0) == (len(set(function)) == 1)), 'hamming_path_and_zero_iff_constant')

    for sample in range(3):
        p = normalize([RNG.randint(1, 13) for _ in omega])
        forms, kernels = block_forms(omega, p)
        d = combine(n, [(1, forms[(x,)]) for x in range(v)])
        ratios = [p[i] / reference[i] for i in range(n)]
        lower, upper = min(ratios), max(ratios)
        check(psd(combine(n, [(1, d), (-lower, reference_dirichlet)])),
              'density_lower_dirichlet_all_functions')
        check(psd(combine(n, [(upper, variance_matrix(reference)), (-1, variance_matrix(p))])),
              'density_upper_variance_all_functions')
        check(psd(combine(n, [(1, d), (-lower / upper, variance_matrix(p))])),
              'density_gap_all_functions')

        all_blocks = list(forms)
        full = tuple(range(v))
        families = [[], [()], [full], [full, full], all_blocks + [full, ()]]
        for family in families:
            multiplicity = [sum(x in block for block in family) for x in range(v)]
            bound = max(multiplicity, default=0)
            weighted = combine(n, [(multiplicity[x], forms[(x,)]) for x in range(v)])
            check(psd(combine(n, [(bound, d), (-1, weighted)])),
                  'multiplicity_all_functions')

            # For every conditional law, verify a common positive Poincare g
            # directly as an exact PSD matrix inequality.
            conditional_data = []
            gap = F(1)
            for block in family:
                local_states = states(tuple(shape[x] for x in block))
                for i, _ in enumerate(omega):
                    q = [sum(kernels[block][i][j] for j, tau in enumerate(omega)
                             if tuple(tau[x] for x in block) == local)
                         for local in local_states]
                    check(min(q) > 0 and sum(q) == 1, 'block_law_positive_probability')
                    gap = min(gap, min(q) / max(q))
                    conditional_data.append((local_states, q))
            for local_states, q in conditional_data:
                local_forms, _ = block_forms(local_states, q)
                local_d = combine(len(q), [(1, local_forms[(x,)])
                                           for x in range(len(local_states[0]))])
                check(psd(combine(len(q), [(1, local_d), (-gap, variance_matrix(q))])),
                      'conditional_gap_premise_all_functions')
            labelled = combine(n, [(1, forms[block]) for block in family])
            check(psd(combine(n, [(1, weighted), (-gap, labelled)])),
                  'conditional_comparison_all_functions')

            if family:
                average = combine(n, [(F(1, len(family)), kernels[block]) for block in family])
                check(stochastic_reversible(p, average), 'block_average_reversibility')
                check(kernel_form_matrix(p, average, len(family)) == labelled,
                      'block_average_form_matrix_identity')

        for rate in (F(0), F(1, 3), F(1)):
            kernel = [[rate * F(i == j) + (1 - rate) * p[j] for j in range(n)] for i in range(n)]
            check(stochastic_reversible(p, kernel), 'refresh_kernel_reversibility')
            for i, sigma in enumerate(omega):
                for j, tau in enumerate(omega):
                    if hamming(sigma, tau) != 1:
                        continue
                    coupling = [[rate * F(a == i and b == j) + (1 - rate) * p[a] * F(a == b)
                                 for b in range(n)] for a in range(n)]
                    check(all(sum(coupling[a]) == kernel[i][a] for a in range(n))
                          and all(sum(coupling[a][b] for a in range(n)) == kernel[j][b] for b in range(n))
                          and min(value for row in coupling for value in row) >= 0,
                          'neighbor_coupling_marginals')
                    check(sum(coupling[a][b] * hamming(omega[a], omega[b])
                              for a in range(n) for b in range(n)) == rate,
                          'neighbor_coupling_cost')
            for function in functions[:40]:
                check(lipschitz(omega, apply(kernel, function)) == rate * lipschitz(omega, function),
                      'lipschitz_coupling_contraction')
            for i in range(n):
                centered = [F(i == j) - p[i] for j in range(n)]
                check(mean(p, centered) == 0
                      and apply(kernel, centered) == [rate * value for value in centered],
                      'centered_eigenvectors')
            if rate < 1:
                scale = F(7, 3)
                gap = scale * (1 - rate)
                check(0 < gap <= scale, 'spectral_constants')
                check(psd(combine(n, [(1, kernel_form_matrix(p, kernel, scale)),
                                      (-gap, variance_matrix(p))])), 'spectral_gap_all_functions')

        # A signed, non-stochastic K is valid in LipschitzEigenvalueStatement.
        eigenvalue = F(-1, 3)
        signed = [[eigenvalue * F(i == j) + 2 * p[j] for j in range(n)] for i in range(n)]
        for function in functions[:10]:
            check(lipschitz(omega, apply(signed, function)) == abs(eigenvalue) * lipschitz(omega, function),
                  'signed_kernel_lipschitz')
        centered = [F(i == 0) - p[0] for i in range(n)]
        if n > 1:
            check(mean(p, centered) == 0 and any(centered)
                  and apply(signed, centered) == [eigenvalue * value for value in centered]
                  and eigenvalue <= abs(eigenvalue), 'signed_kernel_eigenvalue')

        # Rational real/imaginary components check the complex form split.
        real = [F(RNG.randint(-4, 4)) for _ in omega]
        imag = [F(RNG.randint(-4, 4)) for _ in omega]
        variance = sum(p[i] * ((real[i] - mean(p, real)) ** 2
                              + (imag[i] - mean(p, imag)) ** 2) for i in range(n))
        check(variance == quadratic(variance_matrix(p), real) + quadratic(variance_matrix(p), imag),
              'complex_variance_split')
        matrix = kernel_form_matrix(p, kernels[full], F(3))
        kr, ki = apply(kernels[full], real), apply(kernels[full], imag)
        complex_form_real = 3 * sum(p[i] * (real[i] * (real[i] - kr[i])
                                          + imag[i] * (imag[i] - ki[i])) for i in range(n))
        check(complex_form_real == quadratic(matrix, real) + quadratic(matrix, imag),
              'complex_kernel_form_split')

# A reversible stochastic kernel with a negative eigenvalue needs no PSD premise.
p = [F(1, 2), F(1, 2)]
swap = [[F(0), F(1)], [F(1), F(0)]]
check(stochastic_reversible(p, swap) and apply(swap, [1, -1]) == [-1, 1],
      'negative_eigenvalue_reversible_kernel')
check(psd(combine(2, [(1, kernel_form_matrix(p, swap, 1)), (-1, variance_matrix(p))])),
      'negative_eigenvalue_gap_at_c_equals_A')

check(states(()) == [()] and states((0,)) == [], 'empty_product_vs_empty_alphabet')
check(sum([]) != 1, 'empty_configuration_probability_impossible')

result = {'arithmetic': 'exact rational', 'shapes': [list(s) for s in SHAPES],
          'assertions': sum(COUNTS.values()), 'checks': dict(sorted(COUNTS.items()))}
Path(__file__).with_name('finite_checks.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
