#!/usr/bin/env python3
"""Recheck archived H1 choices: direct Gram residuals, then Bareiss fallback.

No representation, inversion, shift or factor search. Inputs stay read only.
The source constructor is used with exact integer overflow guards for its
nonnegative contractions. Every Bareiss division is checked with divmod.
"""
import argparse
import itertools
import json
import math
import os
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path('/home/ubuntu/aklt/compfeas')
HERE = Path(__file__).resolve().parent
OUT = HERE/'checks'
OUT.mkdir(exist_ok=True)
CHOICES = ROOT/'programs/h1-local/out/certificates_covered_operator_only.jsonl'


def worker(part, parts, limit=None):
    sys.dont_write_bytecode = True
    sys.path[:0] = ['/tmp/rev_c2_numpy', str(ROOT/'programs/h1-local/code')]
    import numpy as np
    import ring
    import cert
    ring.P63 = str(ROOT/'programs/data/pext/pext7962.json')
    patterns = ring.load()
    records = [json.loads(s) for s in CHOICES.read_text().splitlines()]
    assert len(patterns) == len(records) == 7962
    assert {r['pid'] for r in records} == set(range(7962))
    assert len({r['pid'] for r in records}) == len(records)
    records = records[part::parts]
    if limit is not None:
        records = records[:limit]
    stats = dict(patterns=0, blocks=0, gram_direct=0, bareiss=0,
                 divisions=0, pivots=0, max_pivot_bits=0, max_dimension=0,
                 contractions=0, max_contraction_bound_bits=0,
                 nonexact_divisions=0, failures=0)
    active = None
    block_rows = []

    def td(a, b, axes):
        assert a.dtype == b.dtype == np.int64
        assert int(a.min(initial=0)) >= 0 and int(b.min(initial=0)) >= 0
        shared = math.prod(a.shape[j] for j in axes[0])
        assert shared == math.prod(b.shape[j] for j in axes[1])
        bound = int(a.max(initial=0))*int(b.max(initial=0))*shared
        assert bound < 2**63, ('contraction bound', active, bound)
        stats['contractions'] += 1
        stats['max_contraction_bound_bits'] = max(stats['max_contraction_bound_bits'], bound.bit_length())
        return np.tensordot(a, b, axes=axes)

    cert.itensordot = td

    def cur_next(net):
        # Same contraction formula as the source, with integer guards before
        # weighted additions instead of a floating shadow.
        z = net.ring({})
        correlations = {}
        for x, y in ((ring.E, ring.N), (ring.E, ring.W), (ring.N, ring.W)):
            if x in net.p.vn and y in net.p.vn:
                terms = [net.ring({x: k, y: k}) for k in (1, 2, 3)]
                assert sum(int(t.max(initial=0)) for t in terms) < 2**63
                correlations[frozenset((x, y))] = sum(terms)
        assert 3*int(z.max(initial=0))+sum(int(c.max(initial=0)) for c in correlations.values()) < 2**63
        cur = 3*z+sum(correlations.values())
        fg = correlations[frozenset(net.p.fg)] if len(net.p.fg) == 2 else 0
        fg_bound = int(fg.max(initial=0)) if isinstance(fg, np.ndarray) else 0
        assert 5*int(z.max(initial=0))+fg_bound < 2**63
        nxt = 5*z+fg
        assert cur.dtype == nxt.dtype == np.int64
        return cur, nxt

    cert.Net.cur_next_int = cur_next
    original_mtensor = cert.mtensor

    def mtensor(k, kind):
        assert 0 <= k <= 4, (active, k, kind)
        tensor, denominator = original_mtensor(k, kind)
        assert isinstance(denominator, int) and denominator > 0
        # The archived constructor obtains this tiny tensor via exact Fractions.
        # Independently check every entry against that rational formula.
        for indices in itertools.product(range(4), repeat=k):
            value = cert.mom_unif(indices)
            if kind == 'd':
                value = cert.Fr(3, 5)*value+(cert.Fr(2, 5) if all(j == 0 for j in indices) else cert.Fr(0))
            value *= denominator
            assert value.denominator == 1 and 0 <= value.numerator < 2**52
            assert int(tensor[indices]) == value.numerator
        return tensor, denominator

    cert.mtensor = mtensor
    original_operator = cert.operator_sym

    def operator(net, coefficients, inverted):
        # A tensor-basis matrix entry uses at most 2**n Pauli terms.
        # Each retained pair basis column has at most two signed entries,
        # adding a factor at most four per pair for a Hermitian form entry.
        pairs = sum(len(s) == 2 for s in net.site_slots.values())
        bound = int(coefficients.max(initial=0))*2**(net.n+2*pairs)
        if bound >= 2**61:
            return cert._operator_sym(net, coefficients, inverted, object)
        return original_operator(net, coefficients, inverted)

    cert.operator_sym = operator

    def positive(matrix):
        n = len(matrix)
        assert all(len(row) == n for row in matrix)
        assert all(matrix[i][j] == matrix[j][i] for i in range(n) for j in range(n))
        stats['blocks'] += 1
        stats['max_dimension'] = max(stats['max_dimension'], n)
        margin = min(matrix[i][i]-sum(abs(matrix[i][j]) for j in range(n) if j != i) for i in range(n))
        if margin > 0:
            stats['gram_direct'] += 1
            block_rows.append(dict(n=n, route='Gram-L0', minimum_residual_margin=margin))
            return True, None
        # Remove a checked positive common scalar only to reduce integer sizes.
        common = math.gcd(*(abs(x) for row in matrix for x in row)) or 1
        a = []
        for row in matrix:
            quotients = []
            for x in row:
                q, r = divmod(x, common)
                assert r == 0
                quotients.append(q)
            a.append(quotients)
        previous = 1
        bit_max = 0
        count_div = 0
        for k in range(n):
            pivot = a[k][k]
            assert pivot > 0, (active, n, k, pivot)
            bit_max = max(bit_max, pivot.bit_length())
            stats['pivots'] += 1
            for i in range(k+1, n):
                aik = a[k][i]
                for j in range(i, n):
                    numerator = pivot*a[i][j]-aik*a[k][j]
                    quotient, remainder = divmod(numerator, previous)
                    assert remainder == 0, ('nonexact division', active, n, k, i, j)
                    a[i][j] = quotient
                    count_div += 1
            previous = pivot
        stats['divisions'] += count_div
        stats['max_pivot_bits'] = max(stats['max_pivot_bits'], bit_max)
        stats['bareiss'] += 1
        block_rows.append(dict(n=n, route='Bareiss-fallback', positive_scalar=common,
                               positive_pivots=n, exact_divisions=count_div, max_pivot_bits=bit_max))
        return True, None

    cert.bareiss_pd = positive
    started = time.monotonic()
    suffix = f'{part}-{parts}' if limit is None else f'{part}-{parts}-probe'
    with (OUT/f'h1_fallback_{suffix}.jsonl').open('w', buffering=1) as stream:
        for index, record in enumerate(records):
            active = record['pid']
            assert record['kind'] == 'operator' and record['model'] == 'covered'
            assert record['tiprad'] == '3/5'
            assert tuple(record['out']) == tuple(patterns[active]['out'])
            threshold = '961/1000' if tuple(record['out']) == (0, 1) else '187/200'
            assert record['target'] == threshold
            assert isinstance(record['leafred'], bool)
            c = cert.Certificate(patterns[active], refined=False, leafred=record['leafred'])
            assert c.net.scale > 0 and c.n == record['n']
            inversions = record['S']
            assert len(set(inversions)) == len(inversions)
            assert all(0 <= i < c.n for i in inversions)
            p, q = map(int, threshold.split('/'))
            block_rows.clear()
            result = c.exact(tuple(inversions), p, q, least_only=True)
            assert result['ok'], (active, result)
            assert len(block_rows) == len(result['sectors'])
            stream.write(json.dumps(dict(pid=active, slots=c.n, D0=c.net.scale,
                                         sectors=result['sectors'], blocks=list(block_rows),
                                         flags=result['flags'], ok=True))+'\n')
            stats['patterns'] += 1
            if (index+1) % 50 == 0:
                print('part', part, 'patterns', stats['patterns'], '/', len(records),
                      'blocks', stats['blocks'], 'seconds', round(time.monotonic()-started, 2), flush=True)
    stats['wall_seconds'] = time.monotonic()-started
    (OUT/f'h1_fallback_{suffix}_summary.json').write_text(json.dumps(stats, indent=2)+'\n')
    print(json.dumps(stats), flush=True)


def run_all():
    env = dict(os.environ, OPENBLAS_NUM_THREADS='1', OMP_NUM_THREADS='1',
               MKL_NUM_THREADS='1', NUMEXPR_NUM_THREADS='1', PYTHONDONTWRITEBYTECODE='1')
    jobs = []
    for part in range(3):
        log = (OUT/f'h1_fallback_{part}-3.out').open('w')
        jobs.append((subprocess.Popen([sys.executable, str(Path(__file__)), '--part', str(part), '--parts', '3'],
                                      env=env, stdout=log, stderr=subprocess.STDOUT), log))
    bad = []
    for process, log in jobs:
        if process.wait() != 0:
            bad.append(process.returncode)
        log.close()
    assert not bad, bad
    totals = [json.loads((OUT/f'h1_fallback_{p}-3_summary.json').read_text()) for p in range(3)]
    combined = {k: sum(row[k] for row in totals) for k in totals[0]
                if k not in ('wall_seconds', 'max_pivot_bits', 'max_dimension', 'max_contraction_bound_bits')}
    for k in ('max_pivot_bits', 'max_dimension', 'max_contraction_bound_bits'):
        combined[k] = max(row[k] for row in totals)
    assert combined['patterns'] == 7962
    assert combined['blocks'] == 12173
    assert combined['gram_direct'] == 8439 and combined['bareiss'] == 3734
    combined['workers'] = 3
    combined['worker_wall_seconds'] = [row['wall_seconds'] for row in totals]
    (OUT/'h1_fallback_summary.json').write_text(json.dumps(combined, indent=2)+'\n')
    print(json.dumps(combined, indent=2), flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--part', type=int)
    parser.add_argument('--parts', type=int, default=3)
    parser.add_argument('--limit', type=int)
    args = parser.parse_args()
    if args.part is None:
        run_all()
    else:
        worker(args.part, args.parts, args.limit)
