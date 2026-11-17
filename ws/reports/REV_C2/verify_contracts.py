#!/usr/bin/env python3
"""Read-only exact checks of the archived C2 inputs; outputs stay in REV_C2.

This is native evidence, not a Lean verification. No witness is searched for.
"""
from collections import Counter
from fractions import Fraction as F
from pathlib import Path
import argparse
import json
import math
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
SOURCE = Path('/home/ubuntu/aklt/compfeas')
OUT = HERE / 'checks'
OUT.mkdir(exist_ok=True)
DIRS = ((1, 0), (0, 1), (-1, 0), (0, -1))
Q = F(1119948287353, 1120437614225)
H = F(5404319552844595, 4503599627370496)


def bond(p, d):
    delta = DIRS[d]
    other = (p[0] + delta[0], p[1] + delta[1])
    return tuple(sorted((p, other))), other


def generate(m):
    def rec(ds, p, used):
        if len(ds) == m:
            yield ds
            return
        for d in range(4):
            edge, other = bond(p, d)
            if edge not in used:
                yield from rec(ds + (d,), other, used | {edge})
    return list(rec((), (0, 0), set()))


def transitions(ds):
    p = (0, 0)
    departed, used = set(), set()
    for d in ds:
        departed.add(p)
        edge, p = bond(p, d)
        used.add(edge)
    for d in range(4):
        edge, other = bond(p, d)
        if edge in used:
            continue
        kind = 2 if p in departed else 0 if d == ds[-1] else 1
        yield d, kind, ds[1:] + (d,)


def little(ds):
    return sum(d * 4**i for i, d in enumerate(ds))


def big(ds):
    return sum(d * 4**(len(ds) - 1 - i) for i, d in enumerate(ds))


def canonical(ds):
    return min(little(tuple((sign * d + rot) % 4 for d in ds))
               for sign in (1, -1) for rot in range(4))


def small_checks():
    result = {}
    counts = [len(generate(m)) for m in range(1, 11)]
    assert counts == [4, 12, 36, 108, 316, 916, 2628, 7500, 21268, 60092]
    result['raw_window_counts_1_through_10'] = counts
    ws = generate(6)
    archive = json.loads((SOURCE / 'data/h2_exact_m6k1_r5.json').read_text())
    rows = archive['rows']
    vector = {r['code']: r['h'] for r in rows}
    assert len(rows) == len(vector) == 115
    assert set(vector) == {canonical(ds) for ds in ws}
    assert all(isinstance(v, int) and v > 0 for v in vector.values())
    numerators = (935000, 961000, 539121)
    ratios, sums, orbit_sizes = {}, {}, Counter(canonical(ds) for ds in ws)
    for ds in ws:
        code = canonical(ds)
        total = sum(numerators[k] * vector[canonical(succ)]
                    for _, k, succ in transitions(ds))
        assert total * Q.denominator <= Q.numerator * 2695605 * vector[code]
        ratios[little(ds)] = F(total, 2695605 * vector[code])
        if code in sums:
            assert sums[code] == total
        sums[code] = total
    for row in rows:
        assert row['sum'] == sums[row['code']]
        assert row['den'] == 2695605
        assert row['orbit_size'] == orbit_sizes[row['code']]
    assert max(ratios.values()) == Q
    assert F(max(vector.values()), min(vector.values())) == F(250000000000, 46594269069)
    assert F(999, 1000) < Q < F(2499, 2500) < 1
    assert 6 * (F(200, 187) / Q)**6 < 10
    result['H2'] = dict(raw_rows=916, orbit_rows=115,
                        max_ratio=str(max(ratios.values())),
                        maximizing_little_codes=[k for k, v in ratios.items() if v == Q],
                        min_v=min(vector.values()), max_v=max(vector.values()),
                        finite_base_majorant=str(6 * (F(200, 187) / Q)**6))

    lines = (SOURCE / 'data/windows_m10_min.txt').read_text().splitlines()
    nraw, nclass = map(int, lines[0].split())
    assert (nraw, nclass) == (60092, 3741)
    assert len(lines) == 1 + nraw + nclass
    mapping_rows = [tuple(map(int, line.split())) for line in lines[1:1+nraw]]
    mapping = dict(mapping_rows)
    raw = generate(10)
    assert [code for code, _ in mapping_rows] == [big(ds) for ds in raw]
    assert set(mapping.values()) == set(range(nclass))
    representatives = [tuple(map(int, line.split())) for line in lines[1+nraw:]]
    edge_counts = Counter()
    for c, row in enumerate(representatives):
        assert len(row) == 9 and mapping[row[0]] == c
        edge_counts.update(k for k in row[5:] if k >= 0)
    for ds in raw:
        row = representatives[mapping[big(ds)]]
        ts = {d: (k, mapping[big(succ)]) for d, k, succ in transitions(ds)}
        for d in range(4):
            if d not in ts:
                assert row[1+d] == row[5+d] == -1
            else:
                k, successor = ts[d]
                assert (row[5+d], row[1+d]) == (k, successor)
                if k != 2:
                    assert ds[-1] == row[0] % 4
    assert edge_counts == Counter({0: 2516, 1: 5032, 2: 1872})
    result['automaton10'] = dict(raw=nraw, classes=nclass,
                                 edges_by_kind=dict(edge_counts), checked_raw_rows=len(raw))

    # Regenerate every coefficient ceiling in the archived C header.
    xs, xt = F(1000, 961), F(200, 187)
    alpha = [F(145217, 10**6), F(150000, 10**6)]
    beta = [F(352782, 10**6), F(357549, 10**6)]
    prime = [F(340008, 10**6), F(344661, 10**6)]
    scale = 2**48
    def ceiling(v):
        return (scale * v.numerator + v.denominator - 1) // v.denominator
    def hp(d, e):
        return F(1) if d % 2 == e % 2 else H
    expected_resp = []
    for arrival in range(4):
        for d in range(4):
            for dead in range(5):
                if d == (arrival + 2) % 4:
                    expected_resp.append(0)
                    continue
                f, g = [j for j in range(4) if j not in ((arrival+2)%4, d)]
                ty = int(d != arrival)
                if dead == f:
                    kappa = prime[ty] * hp(g, d)
                elif dead == g:
                    kappa = prime[ty] * hp(f, d)
                else:
                    kappa = alpha[ty] * hp(f, g) + beta[ty] * (hp(f, d) + hp(g, d))
                expected_resp.append(ceiling((xt if ty else xs) * kappa / 3))
    header = (SOURCE / 'experiments/stationary_weights.h').read_text()
    diagonal = tuple(map(int, re.search(r'qs=(\d+),qt=(\d+),q3=(\d+),q5=(\d+)', header).groups()))
    assert diagonal == tuple(map(ceiling, (xs/3, xt/3, F(1, 3), F(1, 5))))
    resp_text = header.split('qresp[4][4][5] = {', 1)[1]
    assert list(map(int, re.findall(r'\d+', resp_text))) == expected_resp
    result['coefficient_ceilings'] = dict(diagonal=diagonal, response_entries=len(expected_resp))

    phase_coefficients = [F(1, 3), F(1, 5), xs/3, xt/3]
    for arrival in range(4):
        for d in range(4):
            if d == (arrival+2) % 4:
                continue
            f, g = [j for j in range(4) if j not in ((arrival+2)%4, d)]
            ty = int(d != arrival)
            for dead_f in (False, True):
                for dead_g in (False, True):
                    if dead_f and dead_g:
                        reward = F(0)
                    elif dead_f:
                        reward = prime[ty]*hp(g, d)
                    elif dead_g:
                        reward = prime[ty]*hp(f, d)
                    else:
                        reward = alpha[ty]*hp(f, g)+beta[ty]*(hp(f, d)+hp(g, d))
                    phase_coefficients.append((xs if ty == 0 else xt)*reward/3)
    common = math.lcm(*(v.denominator for v in phase_coefficients))
    assert common == 12139925673538045870080000
    result['exact_prefix_common_denominator'] = common

    def f_bounds(s):
        t = (1-s)/(1+s)
        low = 2 * sum((t**(2*k+1)/F(2*k+1) for k in range(8)), F(0)) / (1-s)
        return low, low + 2*t**17 / (17*(1-t*t)*(1-s))
    a = F(116, 125)
    for j, c in enumerate((F(961, 1000), F(187, 200))):
        low_a, _ = f_bounds(a)
        _, upper_ac = f_bounds(a*c)
        _, upper_c = f_bounds(c)
        assert upper_ac/3-low_a/5 <= alpha[j]
        assert upper_ac/3 <= beta[j]
        assert upper_c/3 <= prime[j] <= beta[j]
    result['logarithmic_mean_endpoint_inequalities'] = True

    summary = json.loads((SOURCE / 'logs/final_stationary_summary.json').read_text())
    limits = (351207554, 290599163, 527872005, 380754375, 273048088)
    js = [F(c['bound']) for c in summary['cases']]
    assert all(j*10**9 <= limit for j, limit in zip(js, limits))
    rho = F(993015, 10**6)
    assert F(2*limits[0]+limits[1], 10**9) <= rho
    assert F(sum(limits[2:]), 10**9) <= rho*H
    result['logged_prefix_and_assembly'] = dict(
        nine_digit_ceilings=limits, row_B_ceiling=str(F(2*limits[0]+limits[1], 10**9)),
        row_C_ceiling=str(F(sum(limits[2:]), 10**9)),
        C_integer_slack=(rho*H-F(sum(limits[2:]), 10**9)).numerator)
    (OUT/'small_checks.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2), flush=True)


def stationary_checks():
    for x, ds in [('B', (1, 2)), ('C', (1, 2, 3))]:
        for d in ds:
            name = f'stationary_{x}_m10_R70_d{d}_coarse'
            command = ['env', f'AUTOMATON={SOURCE}/data/windows_m10_min.txt',
                       str(HERE/'check_stationary_integer'), str(SOURCE/'data'/f'{name}.bin.gz'), x, str(d)]
            completed = subprocess.run(command, text=True, capture_output=True)
            (OUT/f'{name}_integer.txt').write_text(completed.stdout+completed.stderr)
            print(name, completed.stdout.strip(), flush=True)
            assert completed.returncode == 0, completed.stderr


def prefix_checks():
    # Preserve the archived evaluator, replacing NumPy's storage with stdlib
    # arrays and redirecting outputs. All weights/enumeration remain unchanged.
    original = (SOURCE/'experiments/exact_stationary_prefix.py').read_text()
    adapted = original.replace(
        "root=Path(__file__).resolve().parents[1];sys.path.insert(0,str(root/'vendor'))\nimport numpy as np",
        f"root=Path({str(SOURCE)!r})\noutdir=Path({str(OUT)!r})\nfrom array import array")
    adapted = adapted.replace('posidx=np.array(positions,dtype=int)', 'posidx=positions')
    adapted = adapted.replace("z=np.frombuffer(zr,dtype='<u4').reshape(4,nw)\n assert np.all(z[2:,:]>=65536)",
                              "z=array('I');z.frombytes(zr)\n assert sys.byteorder=='little' and z.itemsize==4\n assert all(v>=65536 for v in z[2*nw:])")
    adapted = adapted.replace('U=np.empty((4,nw,len(positions)),dtype=np.uint32)', 'U=[[] for _ in range(4)]')
    adapted = adapted.replace("U[p,w,:]=np.frombuffer(block,dtype='<u4')[posidx]",
                              "values=array('I');values.frombytes(block)\n   U[p].append(array('I',(values[j] for j in posidx)))")
    for p in range(4):
        adapted = adapted.replace(f'U[{p},w,j]', f'U[{p}][w][j]')
    adapted = adapted.replace("(root/'logs'/f'{name}_exact_prefix.json')", "(outdir/f'{name}_exact_prefix.json')")
    assert 'np.' not in adapted
    local = HERE/'prefix_checker.py'
    local.write_text('# Adapted storage/output only; see verify_contracts.py.\n'+adapted)
    expected = json.loads((SOURCE/'logs/final_stationary_summary.json').read_text())['cases']
    for case in expected:
        name = case['name']
        completed = subprocess.run([sys.executable, str(local), name], text=True, capture_output=True)
        (OUT/f'{name}_prefix.txt').write_text(completed.stdout+completed.stderr)
        assert completed.returncode == 0, completed.stderr
        observed = json.loads((OUT/f'{name}_exact_prefix.json').read_text())
        assert F(observed['exact_bound']) == F(case['bound'])
        for key in ('prefix_nodes', 'leaves', 'closed', 'phase_multiplications'):
            assert observed[key] == case[key]
        print(name, 'exact prefix fraction and counts match archive', flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('mode', choices=('small', 'stationary', 'prefix'))
    mode = parser.parse_args().mode
    {'small': small_checks, 'stationary': stationary_checks, 'prefix': prefix_checks}[mode]()
