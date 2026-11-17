#!/usr/bin/env python3
"""Fail unless the Audit transcript contains every expected standard-axiom print."""
import argparse
from pathlib import Path
import re

ap = argparse.ArgumentParser(description=__doc__)
ap.add_argument('transcript', type=Path)
args = ap.parse_args()
text = args.transcript.read_text()
expected = {'AKLT.Final.main_of_inputs', 'AKLTPalomar.h1_iff', 'AKLTPalomar.h3_iff',
            'AKLTPalomar.main_iff', 'AKLTPalomar.aklt_gap_of_inputs'}
permitted = {'propext', 'Classical.choice', 'Quot.sound'}
seen = set()
for name, values in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text):
    if name not in expected:
        continue
    axioms = {v.strip() for v in values.split(',') if v.strip()}
    if not axioms <= permitted:
        raise SystemExit(f'Forbidden axiom for {name}: {sorted(axioms-permitted)}')
    seen.add(name)
if seen != expected:
    raise SystemExit(f'Missing audit prints: {sorted(expected-seen)}')
print(f'PASS: all {len(expected)} exports use only the three permitted axioms')
