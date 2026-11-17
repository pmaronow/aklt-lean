#!/usr/bin/env python3
"""Exact arithmetic, registry and finite geometry checks for section 7.

Uses only the Python standard library; never writes to an input directory.
The geometry checks are finite sanity checks, not certificates for H3_h.
"""

from collections import Counter
from fractions import Fraction as F
import json
from math import lcm
from pathlib import Path
import re


HERE = Path(__file__).resolve().parent
PLAN = Path('/home/ubuntu/aklt/reports/REV-PLAN/PLAN.md')
WALK_SECTION = Path('/home/ubuntu/aklt/reports/REV_C1a/sec6-walks.tex')


def bounds(s):
    t = (1 - s) / (1 + s)
    lo = 2 * sum((t ** (2 * k + 1) / (2 * k + 1)
                  for k in range(8)), F(0)) / (1 - s)
    return lo, lo + 2 * t**17 / (17 * (1 - t*t) * (1 - s))


def statement_check():
    plan = PLAN.read_text().split(
        '## 7. Pair closure, a positive-vector witness, and renewal', 1
    )[1].split('## 8. Exact statements', 1)[0]
    tex = (HERE / 'sec7-recursion.tex').read_text()
    planned = re.findall(r'```latex\n(.*?)\n```', plan, re.S)
    normalize = lambda s: re.sub(r'\s+', ' ', s).strip()
    result = []
    positions = []
    for frag in planned:
        label = re.search(r'\\label\{([^}]+)\}', frag)[1]
        env = re.search(r'\\begin\{([^}]+)\}', frag)[1]
        needle = '\\label{' + label + '}'
        pos = tex.index(needle)
        positions.append(pos)
        begin = tex.rfind('\\begin{' + env + '}', 0, pos)
        end = tex.index('\\end{' + env + '}', pos) + len('\\end{' + env + '}')
        actual = tex[begin:end]
        exact = normalize(actual) == normalize(frag)
        if label == 'l:terminalcover':
            assert not exact
            corrected_back = actual.replace(
                'assume also that \\(v\\notin S\\), and\n', '')
            assert normalize(corrected_back) == normalize(frag)
        else:
            assert exact, label
        result.append({'label': label, 'exact_registry_text': exact})
    assert len(result) == 12
    assert positions == sorted(positions), 'statement order differs from registry'
    assert tex.count('\\begin{proof}') == 8
    assert tex.count('\\end{proof}') == 8
    labels = re.findall(r'\\label\{([^}]+)\}', tex)
    assert len(labels) == len(set(labels)), 'duplicate label'
    refs = set(re.findall(r'\\(?:eqref|ref)\{([^}]+)\}', tex))
    external = sorted(refs - set(labels))
    allowed = {
        'd:domain', 'd:moment', 'd:pattern', 'd:pinmodel', 'd:ratios',
        'd:trace', 'd:weights', 'h:H1', 'h:H2',
        'h:P', 'l:35', 'l:exposure', 'l:finitefacts', 'l:local',
        'l:onepoint', 'l:response', 'p:pairwalk',
    }
    assert set(external) == allowed
    (HERE / 'external-labels.txt').write_text('\n'.join(external) + '\n')
    return {'statements': result, 'external_labels': external,
            'complete_proof_environments': 8}


def arithmetic_check():
    a = F(116, 125)
    mean_bound = F(3, 5)
    sum_lower = -3*mean_bound**2/2
    sum_upper = 3*mean_bound**2
    i_lower, i_upper = 1+sum_lower/3, 1+sum_upper/3
    j_lower, j_upper = 1-mean_bound**2/5, 1+mean_bound**2/5
    assert (i_lower, i_upper) == (F(41, 50), F(34, 25))
    assert (j_lower, j_upper) == (F(116, 125), F(134, 125))
    alpha_lower = 1/(3*i_upper) - 1/(5*j_lower)
    assert alpha_lower == F(175, 5916) > 0
    endpoint_data = [
        (a, F(9, 241), 1037827030, 1037827031),
        (a * F(961, 1000), F(3381, 59119), 1058344574, 1058344575),
        (a * F(187, 200), F(827, 11673), 1072644315, 1072644316),
        (F(961, 1000), F(39, 1961), 1020022307, 1020022308),
        (F(187, 200), F(13, 387), 1033980764, 1033980765),
    ]
    K = 10**9
    D = lcm(*range(1, 16, 2))
    assert D == 45045
    endpoint_results = []
    ceilings = {}
    floors = {}
    for s, t, ell, upper in endpoint_data:
        lo, hi = bounds(s)
        assert t == (1-s)/(1+s)
        assert F(ell, K) <= lo <= hi <= F(upper, K)
        u, v, p, q = s.numerator, s.denominator, t.numerator, t.denominator
        P = sum(D // (2*k+1) * p**(2*k+1) * q**(14-2*k)
                for k in range(8))
        Q = (v-u)*D*q**15
        assert lo == F(2*v*P, Q)
        assert hi == F(2*v*(17*(q*q-p*p)*P + D*p**17),
                       17*(q*q-p*p)*Q)
        low_res = 2*v*K*P - ell*Q
        high_res = 17*upper*(q*q-p*p)*Q - 2*v*K*(
            17*(q*q-p*p)*P + D*p**17)
        assert low_res > 0 and high_res > 0
        endpoint_results.append({
            's': str(s), 't': str(t), 'lower': str(lo), 'upper': str(hi),
            'lower_integer_residual': low_res,
            'upper_integer_residual': high_res,
        })
        ceilings[s], floors[s] = upper, ell

    rows = [
        ('s', F(961, 1000), 145217, 352782, 340008, (13215, 1425, 1692)),
        ('t', F(187, 200), 150000, 357549, 344661, (259510, 2684, 2235)),
    ]
    coeff_results = []
    removal_cases = 0
    for kind, c, A, B, BP, residuals in rows:
        aa, bb, bp = F(A, 10**6), F(B, 10**6), F(BP, 10**6)
        assert F(3, 5) <= c <= 1
        assert bounds(a*c)[1]/3 - bounds(a)[0]/5 < aa
        assert bounds(a*c)[1]/3 < bb
        assert bounds(c)[1]/3 < bp
        assert 0 < bp <= bb <= F(36751, 100000)
        assert 0 < aa <= F(18094, 100000)
        actual_res = (15000*A - 5*ceilings[a*c] + 3*floors[a],
                      3000*B - ceilings[a*c], 3000*BP - ceilings[c])
        assert actual_res == residuals
        coeff_results.append({'type': kind, 'residuals': residuals})

        def coefficients(mask):
            if mask == 3:
                return {(0, 1): aa, (0, 2): bb, (1, 2): bb}
            if mask == 1:
                return {(0, 2): bp}
            if mask == 2:
                return {(1, 2): bp}
            return {}

        for kernel_mask in range(4):
            for actual_mask in range(4):
                if actual_mask & kernel_mask != actual_mask:
                    continue
                kc, ac = coefficients(kernel_mask), coefficients(actual_mask)
                assert all(p in kc and value <= kc[p] for p, value in ac.items())
                removal_cases += 1

    h = F(5404319552844595, 4503599627370496)
    rho0 = F(993015, 10**6)
    q = F(1119948287353, 1120437614225)
    cv = F(10)
    assert 1 < h < F(6, 5)
    assert F(6, 5)-h == F(1, 5*4503599627370496)
    assert 0 < q < F(2499, 2500) < 1
    C = F(18094, 100000) + 2*F(36751, 100000)
    b = (1+q)/2
    r = q/b
    Bstar = 2*h*C*cv/b**2 * r/(1-r)**3
    eps = min((1-b)/2, (1-rho0)/(2*Bstar))
    theta, rho = 1-eps, (1+rho0)/2
    assert 0 < q*q < theta < 1
    assert rho0 < rho < 1
    assert Bstar*(1-theta) <= rho-rho0
    ct = 2*F(12, 5)**24 * (cv/(1-q))**2
    prefactor = h*max(F(2), ct)/(1-rho)
    assert prefactor >= 2
    return {
        'logarithm_endpoints': endpoint_results,
        'coefficient_rows': coeff_results,
        'additional_removal_cases': removal_cases,
        'canonical_alpha_positive_lower_bound': str(alpha_lower),
        'example_explicit_shift': {'theta': str(theta), 'epsilon': str(eps),
                                   'rho': str(rho), 'A': str(prefactor)},
    }


def imported_contract_check():
    """Check the referee's six missing contracts against the actual owner."""
    plan = PLAN.read_text()
    walk = WALK_SECTION.read_text()
    contracts = {}
    for label in ['d:trace', 'd:ratios', 'p:pairwalk',
                  'l:local', 'l:exposure', 'l:onepoint']:
        needle = '\\label{' + label + '}'
        planned = next(frag for frag in re.findall(r'```latex\n(.*?)\n```',
                                                  plan, re.S)
                       if needle in frag)
        env = re.search(r'\\begin\{([^}]+)\}', planned)[1]
        pos = walk.index(needle)
        begin = walk.rfind('\\begin{' + env + '}', 0, pos)
        end = walk.index('\\end{' + env + '}', pos) + len('\\end{' + env + '}')
        normalize = lambda s: re.sub(r'\s+', ' ', s).strip()
        assert normalize(walk[begin:end]) == normalize(planned), label
        contracts[label] = {
            'file': str(WALK_SECTION), 'line': walk[:pos].count('\n')+1,
            'matches_exact_plan_statement': True,
        }
        if env in ['lemma', 'proposition']:
            proof = walk.index('\\begin{proof}', end)
            assert proof == walk.index('\\begin{', end), label
            contracts[label]['proof_line'] = walk[:proof].count('\n')+1
    return contracts


def geometry_check():
    dirs = ((1, 0), (0, 1), (-1, 0), (0, -1))
    u, c = (-1, 0), (0, 0)
    counts = {}
    checked_first_visits = 0

    def distance(a, b):
        return abs(a[0]-b[0]) + abs(a[1]-b[1])

    def check_closed(path, target):
        nonlocal checked_first_visits
        n = len(path)-1
        departures = Counter()
        for i, (y, out) in enumerate(zip(path, path[1:])):
            assert out != c and departures[out] < 2
            if departures[y] == 0:
                checked_first_visits += 1
                arrival = c if i == 0 else path[i-1]
                neighbours = [(y[0]+dx, y[1]+dy) for dx, dy in dirs]
                remaining = [z for z in neighbours if z != arrival]
                assert out in remaining and len(remaining) == 3
                for z in remaining:
                    assert 2*min(distance(z, u), distance(z, target)) <= n+2
            departures[y] += 1
        assert n % 2 == 0

    for kind, target, expected in [('B', (1, 0), (937, 922, 937)),
                                   ('C', (0, 1), (715, 1036, 861))]:
        case_counts = Counter()
        path = [u]
        used = set()

        def dfs():
            y = path[-1]
            if y == target:
                check_closed(path, target)
                case_counts[path[1]] += 1
                return
            if len(path)-1 == 12:
                return
            for dx, dy in dirs:
                z = (y[0]+dx, y[1]+dy)
                if z == c:
                    continue
                edge = tuple(sorted((y, z)))
                if edge in used:
                    continue
                used.add(edge)
                path.append(z)
                dfs()
                path.pop()
                used.remove(edge)

        dfs()
        observed = tuple(case_counts[z] for z in [(-1, 1), (-2, 0), (-1, -1)])
        assert observed == expected, (kind, observed)
        counts[kind] = {'north_west_south': observed, 'total': sum(observed)}

    G = {(x, y) for x in range(-3, 4) for y in range(-3, 4)}
    S = {x for x in G if max(map(abs, x)) >= 2}
    centre, start, target = (1, 0), (0, 0), (2, 0)
    w = [(0, 0), (0, 1), (0, 2)]
    assert centre not in S and start not in S and target in S
    assert distance(start, target) == 2
    assert distance(start, centre) == distance(target, centre) == 1
    assert w[-1] in S and all(z not in S for z in w[:-1])
    assert target not in w and centre not in w
    assert all(distance(x, y) == 1 for x, y in zip(w, w[1:]))
    exceptional = {(dx, dy) for dx in range(-2, 3) for dy in range(-2, 3)
                   if 0 < abs(dx)+abs(dy) <= 2}
    assert len(exceptional) == 12
    return {'closed_trails_through_length_12': counts,
            'checked_first_visits': checked_first_visits,
            'terminal_counterexample_verified': True,
            'exceptional_site_count': len(exceptional)}


def main():
    result = {'registry': statement_check(), 'arithmetic': arithmetic_check(),
              'geometry': geometry_check(),
              'imported_contracts': imported_contract_check()}
    (HERE / 'checks.json').write_text(json.dumps(result, indent=2) + '\n')
    print('PASS: 12 statements; one documented hypothesis correction; 8 proofs.')
    print('PASS: 5 logarithm endpoints; 6 coefficient targets; 18 removal cases.')
    print('PASS: exact shifted-witness parameters and renewal prefactor.')
    print('PASS: canonical coefficient positivity; all 6 imports match their owner and plan.')
    print('PASS: 5408 closed trails through length 12; terminal counterexample; 12 sites.')
    print('External references:', ', '.join(result['registry']['external_labels']))


if __name__ == '__main__':
    main()
