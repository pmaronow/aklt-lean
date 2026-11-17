#!/usr/bin/env python3
"""Inline the unchanged statement definitions; never copy a proof layer."""
import argparse
import hashlib
import json
from pathlib import Path
import re


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--tree', type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument('--output', type=Path, default=Path(__file__).resolve().parents[1])
    args = parser.parse_args()
    selection = [
        ('AKLT/Challenge/Main.lean', 'AKLT.Challenge', {
            'Size', 'size_neZero', 'Site', 'Direction', 'Bond', 'nextSite', 'V', 'spinZ', 'spinPlus', 'spinMinus',
            'Configuration', 'Hilbert', 'atSite', 'onBond', 'bondCasimir', 'spin4Space', 'P', 'H',
            'SpinorPolynomial', 'singlet', 'vbsPolynomial', 'monomialDegree', 'B'}),
        ('AKLT/Challenge/MainV2.lean', 'AKLT.Challenge', None),
    ]
    result = '''module

public import Mathlib

/-! The unconditional spin-2 square-lattice AKLT headline.
Definitions are copied faithfully from the statement layers;
no certificate or analytic proof module is imported. See FIDELITY.md. -/

@[expose] public section
set_option backward.proofsInPublic true
noncomputable section
open scoped BigOperators ENNReal
'''
    sources = []
    for relative, namespace, names in selection:
        original = (args.tree / relative).read_text()
        start = original.index('namespace ' + namespace) + len('namespace ' + namespace)
        end = original.rindex('end ' + namespace)
        content = original[start:end].strip()
        offsets = list(re.finditer(r'^/--', content, re.M))
        blocks = [content[m.start():offsets[i+1].start() if i+1 < len(offsets) else len(content)]
                  for i,m in enumerate(offsets)]
        kept = []
        for block in blocks:
            declared = re.findall(r'^(?:@\[[^\n]*\]\s*)*(?:noncomputable )?(?:def|abbrev|inductive|structure|instance) ([\w.]+)', block, re.M)
            if names is None or any(name in names for name in declared):
                kept.append(re.sub(r'^instance size_neZero', '@[expose] instance size_neZero', block.rstrip(), flags=re.M))
        result += '\n/- Statement source: ' + relative + '. -/\n'
        result += ('/- Reset only Lean’s auxiliary-proof cache at the original source boundary,\n'
                   'preserving generated proof names. All declarations remain kernel checked. -/\n'
                   'run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})\n')
        result += 'namespace ' + namespace + '\n\n'
        result += '\n\n'.join(kept) + '\n\nend ' + namespace + '\n'
        sources.append({'source': relative, 'source_sha256': hashlib.sha256(original.encode()).hexdigest(),
                        'declarations': sorted(names) if names is not None else 'all statement declarations'})
    result += '''
namespace AKLTPalomar

/-- Paper t:main: all-period ground-state uniqueness, and an eventual uniform gap. -/
def Main : Prop := AKLT.Challenge.MainStatementV2

/-- The unconditional theorem of the paper, t:main in sec1-result.tex. -/
theorem aklt_gap : Main := by
  sorry

end AKLTPalomar
'''
    assert len(result.splitlines()) <= 1000
    assert len(result.encode()) <= 100 * 1024
    args.output.mkdir(parents=True, exist_ok=True)
    (args.output / 'Challenge.lean').write_text(result)
    (args.output / 'statement-sources.json').write_text(json.dumps(sources, indent=2) + '\n')
    print(f'Challenge: {len(result.splitlines())} physical lines, {len(result.encode())} bytes')


if __name__ == '__main__':
    main()
