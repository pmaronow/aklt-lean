"""Read-only inventory and consistency audit of archived H1 validations."""
import ast
import collections
import hashlib
import json
from fractions import Fraction as F
from pathlib import Path

from audit_math import BUNDLE, DATA, OUT, N, groups, parse, prune

AG = Path('/home/ubuntu/aklt/source-full/agents')
A72 = AG/'72-audit-H1-certificates'
A73 = AG/'73-reimplement-H1'


def readlines(p):
    return [json.loads(l) for l in p.read_text().splitlines()]


def main():
    records = json.loads(DATA.read_text())
    old = json.loads((AG/'63-certify-N/out/pext7962.json').read_text())
    merged = json.loads((AG/'57-vector-channel/out/pext59_merged.json').read_text())
    assert records == old
    assert all(parse(a) == parse(b) for a, b in zip(records, merged)) and len(merged) == 7962
    print('DATA frozen records = 63 records; structures = 57 merged: 7962/7962')
    for name in ('cert.py', 'ring.py', 'closed_exact.py'):
        assert (BUNDLE/'programs/h1-local/code'/name).read_bytes() == (AG/'70-local-bounds/code'/name).read_bytes()
    print('CODE frozen cert.py, ring.py, closed_exact.py = archived 70 copies: byte-identical')
    selected = {c['pid']: c for c in readlines(OUT/'certificates_covered_operator_only.jsonl')}
    for name in ('certificates_covered_operator_only.jsonl', 'certificates_covered.jsonl'):
        assert (OUT/name).read_bytes() == (AG/'70-local-bounds/out'/name).read_bytes()
    print('CERT frozen two covered certificate files = archived 70 copies: byte-identical')

    xcheck = json.loads((A72/'out/xcheck_brute_all.json').read_text())
    print('XCHECK three full untied points:', xcheck)
    su2 = json.loads((A72/'out/su2check_all_summary.json').read_text())
    assert sum(p['su2_checked'] for p in su2['parts']) == 7962 and not su2['su2_fail']
    print('SU2 archived summary:', su2)
    allsample = json.loads((A72/'out/su2_allexact.json').read_text())
    sample = {r['pid'] for r in allsample['rows'] if r['all_sectors_exact']}
    assert len(sample) == 50
    neg = []
    for name in ('negctl_hard.json', 'negctl_random.json'):
        rows = json.loads((A72/'out'/name).read_text())
        ok = {r['pid'] for r in rows if r.get('accept_target_all')}
        neg.extend(ok)
        print('ALL-SECTOR', name, 'positive target records:', len(ok), 'ids', sorted(ok))
    print('ALL-SECTOR 72 sample 50 union negative-control target checks:', len(sample | set(neg)))
    # A second text output contains four additional explicit all-sector spot checks.
    unit = (A72/'out/unitpert.txt').read_text().splitlines()
    mutations = [l for l in unit if 'perturbed coefficient' in l]
    assert len(mutations) == 30 and all(l.endswith('False') for l in mutations)
    print('MUTATION archived output:', len(mutations), 'detected; final:', unit[-1])

    rows = readlines(A73/'out/operator_only_results.jsonl')
    assert sorted(r['pid'] for r in rows) == list(range(7962))
    for r in rows:
        i = r['pid']
        assert r['ok'] and r['all_sectors'] and not r.get('cross_sector_entries', False)
        assert all(b[2] for b in r['blocks'])
        assert (r['leafred'], r['S']) == (selected[i]['leafred'], selected[i]['S'])
        assert F(r['target']) == (F(961, 1000) if tuple(records[i]['out']) == N else F(187, 200))
        assert r['fullspace'] == all(t != 'upair' for t, x in groups(records[i], r['leafred']))
    print('SECOND OPERATOR archived coverage/choices/type-threshold/all-sector results: 7962 PASS')
    print('SECOND OPERATOR fullspace:', sum(r['fullspace'] for r in rows),
          'U-pair complement:', sum(not r['fullspace'] for r in rows),
          'all Sz blocks:', sum(len(r['blocks']) for r in rows))
    closed = readlines(A73/'out/k1_exact.jsonl')
    assert len({r['pid'] for r in closed}) == len(closed) == 4735 and all(r['ok'] for r in closed)
    for r in closed:
        rad = prune(records[r['pid']])
        assert {ast.literal_eval(x): F(v) for x, v in r['radii'].items()} == rad
    print('SECOND CLOSED archived coverage/radii/exact threshold results: 4735 PASS')
    nums = readlines(A73/'out/k1b_numerics.jsonl')
    assert {r['pid'] for r in nums} == {r['pid'] for r in closed}
    print('SECOND NUMERICS decoupled:', len(nums), 'max gap:', max(r['gap'] for r in nums),
          'min(opt_min - closed):', min(r['opt_min']-r['closed'] for r in nums))
    for name in ('cert.py', 'ring.py'):
        p = BUNDLE/'programs/h1-local/code'/name
        print('SHA256', str(p), hashlib.sha256(p.read_bytes()).hexdigest())


if __name__ == '__main__':
    main()
