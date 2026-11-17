#!/usr/bin/env python3
"""Fail unless the Audit transcript contains every expected standard-axiom print."""
import argparse
from pathlib import Path
import re

ap = argparse.ArgumentParser(description=__doc__)
ap.add_argument('transcript', type=Path)
ap.add_argument('--mode', choices=['full','regression','handwritten'], default='full')
args = ap.parse_args()
text = args.transcript.read_text()
expected = ({'CertData.Close.h1','CertData.Close.h2','CertData.Close.h3','CertData.Close.main',
             'AKLTPalomar.main_iff','AKLTPalomar.aklt_gap'} if args.mode=='full' else
            {'AKLT.Final.main_of_inputs','AKLTPalomar.h1_iff','AKLTPalomar.h3_iff',
             'AKLTPalomar.main_iff','AKLTPalomar.aklt_gap_of_inputs'})
if args.mode=='handwritten':
    expected |= {'AKLT.Challenge.bond_rank','AKLT.Challenge.four_by_four_nondegenerate','AKLT.Challenge.b_nonzero','AKLT.Final.main_of_certificates','RegenSamples.H1.checked',
        'RegenSamples.H1.packed_reduces','RegenSamples.H1Consumer.packed_reduces_again',
        'RegenSamples.H1Consumer.lowerTriangular','RegenSamples.H1Consumer.literal_reduces',
        'RegenSamples.H3.checked','RegenSamples.H3.walk_step',
        'RegenSamples.H3Consumer.component_bound','RegenSamples.H3Consumer.literal_reduces'}
permitted = {'propext', 'Classical.choice', 'Quot.sound'}
seen = set()
for name, values in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text):
    if name not in expected:
        continue
    axioms = {v.strip() for v in values.split(',') if v.strip()}
    if not axioms <= permitted:
        raise SystemExit(f'Forbidden axiom for {name}: {sorted(axioms-permitted)}')
    seen.add(name)
seen.update(re.findall(r"'([^']+)' does not depend on any axioms", text))
seen &= expected
if args.mode=='handwritten' and 'FIRST_PARTY_AXIOM_AUDIT_PASS:' not in text:
    raise SystemExit('Missing exhaustive first-party axiom audit marker')
if seen != expected:
    raise SystemExit(f'Missing audit prints: {sorted(expected-seen)}')
print(f'PASS: all {len(expected)} exports use only the three permitted axioms')
