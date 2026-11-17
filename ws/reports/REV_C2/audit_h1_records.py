#!/usr/bin/env python3
"""Relate every rerun sector record and positivity branch to archived choices."""
import json
from pathlib import Path

root = Path('/home/ubuntu/aklt/compfeas')
checks = Path(__file__).resolve().parent/'checks'
patterns = json.loads((root/'programs/data/pext/pext7962.json').read_text())
choices = [json.loads(line) for line in (root/'programs/h1-local/out/certificates_covered_operator_only.jsonl').read_text().splitlines()]
records = [json.loads(line) for part in range(3)
           for line in (checks/f'h1_fallback_{part}-3.jsonl').read_text().splitlines()]
assert len(patterns) == len(choices) == len(records) == 7962
assert len({row['pid'] for row in choices}) == len(choices)
assert len({row['pid'] for row in records}) == len(records)
choices_by_id = {row['pid']: row for row in choices}
records_by_id = {row['pid']: row for row in records}
assert set(choices_by_id) == set(records_by_id) == set(range(7962))
direct = fallback = pivots = divisions = 0
for pid, pattern in enumerate(patterns):
    choice, record = choices_by_id[pid], records_by_id[pid]
    assert choice['kind'] == 'operator' and choice['model'] == 'covered'
    assert choice['tiprad'] == '3/5'
    assert choice['out'] == pattern['out']
    assert tuple(pattern['out']) in ((1, 0), (0, 1), (-1, 0))
    assert choice['target'] == ('961/1000' if tuple(pattern['out']) == (0, 1) else '187/200')
    assert isinstance(choice['leafred'], bool)
    assert record['slots'] == choice['n']
    assert isinstance(record['D0'], int) and record['D0'] > 0
    assert record['ok'] and all(value == 0 for value in record['flags'].values())
    assert len(record['blocks']) == len(record['sectors'])
    for sector, block in zip(record['sectors'], record['blocks']):
        assert sector[1] == block['n'] and sector[2]
        if block['route'] == 'Gram-L0':
            assert block['minimum_residual_margin'] > 0
            direct += 1
        else:
            assert block['route'] == 'Bareiss-fallback'
            assert block['positive_scalar'] > 0
            assert block['positive_pivots'] == block['n']
            assert block['exact_divisions'] >= 0
            fallback += 1
            pivots += block['positive_pivots']
            divisions += block['exact_divisions']
samples = json.loads((checks/'h1_gram_samples.json').read_text())
for sample in samples:
    record = records_by_id[sample['pid']]
    matching = [block for sector, block in zip(record['sectors'], record['blocks'])
                if sector[0] == sample['sector'] and block['n'] == sample['dimension']]
    assert len(matching) == 1 and matching[0]['route'] == 'Bareiss-fallback'
    assert sample['regenerated_matrix_matches'] and sample['strictly_dominant']
    assert sample['minimum_margin'] > 0
assert (direct, fallback, pivots, divisions) == (8439, 3734, 93614, 57970522)
summary = dict(patterns=7962, blocks=direct+fallback,
               checked_threshold_type_out_dimension_denominator_agreement=True,
               direct_Gram_blocks=direct, archived_nonzero_Gram_blocks=len(samples),
               adopted_fallback_blocks=fallback-len(samples),
               native_Bareiss_blocks=fallback, positive_native_pivots=pivots,
               checked_native_divisions=divisions)
(checks/'h1_record_audit.json').write_text(json.dumps(summary, indent=2)+'\n')
print(json.dumps(summary, indent=2))
