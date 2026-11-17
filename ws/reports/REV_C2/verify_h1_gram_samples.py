#!/usr/bin/env python3
"""Check the two archived nonzero Gram factors against regenerated sectors."""
import json
import math
from pathlib import Path
import sys

import numpy as np
import ring
import cert

source = Path('/home/ubuntu/aklt/compfeas')
destination = Path('/home/ubuntu/aklt/reports/REV_C2/checks')
ring.P63 = str(source/'programs/data/pext/pext7962.json')
patterns = ring.load()
records = {r['pid']: r for r in map(json.loads, (source/'programs/h1-local/out/certificates_covered_operator_only.jsonl').read_text().splitlines())}
results = []
for path in sorted((source/'data').glob('h1_chol_*.json')):
    witness = json.loads(path.read_text())
    pid, n = witness['pid'], witness['n']
    record = records[pid]
    p, q = map(int, record['target'].split('/'))
    constructor = cert.Certificate(patterns[pid], refined=False, leafred=record['leafred'])
    aa, bb, labels, flags = constructor.operators(tuple(record['S']))
    assert all(value == 0 for value in flags.values())
    matches = []
    for sector in cert.sector_list(labels, True):
        indices = np.where(labels == sector)[0]
        if len(indices) != n:
            continue
        matrix = [[5*q*int(aa[i, j])-3*p*int(bb[i, j]) for j in indices] for i in indices]
        common = math.gcd(*(abs(x) for row in matrix for x in row)) or 1
        if common != witness['gcd']:
            continue
        if [[x//common for x in row] for row in matrix] == witness['M']:
            matches.append((sector, matrix, common))
    assert len(matches) == 1, (pid, len(matches))
    sector, matrix, g = matches[0]
    d, S = witness['shift_den'], 2**witness['precision']
    lower = witness['L']
    assert g > 0 and d > 0 and S > 0
    assert len(lower) == n and all(len(row) == n for row in lower)
    assert all(isinstance(x, int) for row in lower for x in row)
    assert all(lower[i][j] == 0 for i in range(n) for j in range(i+1, n))
    residual = [[d*S*S*matrix[i][j]-g*sum(lower[i][k]*lower[j][k] for k in range(min(i, j)+1))
                 for j in range(n)] for i in range(n)]
    margins = [residual[i][i]-sum(abs(residual[i][j]) for j in range(n) if i != j) for i in range(n)]
    assert min(margins) > 0
    assert min(margins) == g*witness['min_margin']
    results.append(dict(file=path.name, pid=pid, sector=int(sector), dimension=n,
                        g=g, d=d, S=S, minimum_margin=min(margins),
                        regenerated_matrix_matches=True, strictly_dominant=True))
assert {row['pid'] for row in results} == {5420, 7697}
(destination/'h1_gram_samples.json').write_text(json.dumps(results, indent=2)+'\n')
print(json.dumps(results, indent=2))
