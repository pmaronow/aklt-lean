#!/usr/bin/env python3
"""Generate the independent statement and check its exact reproducibility."""
import argparse
import hashlib
import json
from pathlib import Path
import re

# Main.lean is frozen while certificates are rebuilt. Only copied documentation
# is corrected here; every declaration body is copied without alteration.
COMMENT_CORRECTIONS = {
    '§1, before (`d:model`, `sec1-result.tex`)':
        'Definition 1.1 (`d:model`, `sec1-result.tex`)',
    '§1, the set E': 'Definition 1.1 (`d:model`, `sec1-result.tex`), the set E',
    '§1; §2, (`d:poly`, `sec3-quantum-frames.tex`)':
        'Definition 1.1 (`d:model`, `sec1-result.tex`) and Definition 3.1 (`d:poly`, `sec3-quantum-frames.tex`)',
    '§2, immediately before (`d:model`, `sec1-result.tex`)':
        'Definition 1.1 (`d:model`, `sec1-result.tex`)',
    '§2, (`d:model`, `sec1-result.tex`)':
        'Definition 3.1 (`d:poly`, `sec3-quantum-frames.tex`)',
    'exactly (`d:model`, `sec1-result.tex`)':
        'exactly Definition 1.1 (`d:model`, `sec1-result.tex`)',
    'B of (`d:model`, `sec1-result.tex`)':
        'B of Definition 1.1 (`d:model`, `sec1-result.tex`)',
    'unitary for (`d:poly`, `sec3-quantum-frames.tex`)':
        'unitary for Definition 3.1 (`d:poly`, `sec3-quantum-frames.tex`)',
    '§1, P_e': 'Definition 1.1 (`d:model`, `sec1-result.tex`), P_e',
    '§1, total-spin-4 subspace': 'Definition 1.1 (`d:model`, `sec1-result.tex`), total-spin-4 subspace',
    'P_e of §1:': 'P_e of Definition 1.1 (`d:model`, `sec1-result.tex`):',
    'Together with `spinPlus` and `spinMinus` this fixes the concrete model of V.':
        'Together with `spinPlus` and `spinMinus` this fixes the concrete model of V.\n'
        'The label of e_k under spinZ is the negative of the paper\'s weight for\n'
        'z₁^(4-k) z₂^k; this relabeling preserves the Casimir, projection, and Hamiltonian.',
}


def correct_comments(text):
    """Change prose only, preserving the Lean code and exact paper labels."""
    def replace(match):
        comment = match.group()
        for old, new in COMMENT_CORRECTIONS.items():
            comment = comment.replace(old, new)
        return comment
    return re.sub(r'/\-.*?\-/', replace, text, flags=re.S)


def render(tree):
    selection = [
        ('AKLT/Challenge/Main.lean', 'AKLT.Challenge', {
            'Size', 'size_neZero', 'Site', 'Direction', 'Bond', 'nextSite', 'V', 'spinZ', 'spinPlus', 'spinMinus',
            'Configuration', 'Hilbert', 'atSite', 'onBond', 'bondCasimir', 'spin4Space', 'P', 'H',
            'SpinorPolynomial', 'singlet', 'vbsPolynomial', 'monomialDegree', 'B'}),
        ('AKLT/Challenge/MainV2.lean', 'AKLT.Challenge', None),
    ]
    result = '''module

public import Mathlib

/-! The unconditional spin-2 square-lattice AKLT theorem.
The model, bonds, determinant, VBS product, and Hamiltonian are Definition 1.1
(`d:model`, `sec1-result.tex`); the polynomial model and norm are Definition 3.1
(`d:poly`, `sec3-quantum-frames.tex`); the headline is Theorem 1.2
(`t:main`, `sec1-result.tex`). -/

@[expose] public section
set_option backward.proofsInPublic true
noncomputable section
open scoped BigOperators ENNReal
'''
    sources = []
    for relative, namespace, names in selection:
        original = (tree / relative).read_text()
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
                kept.append(correct_comments(block.rstrip()))
        result += '\n/- Statement source: ' + relative + '. -/\n'
        result += 'namespace ' + namespace + '\n\n'
        result += '\n\n'.join(kept) + '\n\nend ' + namespace + '\n'
        sources.append({'source': relative, 'source_sha256': hashlib.sha256(original.encode()).hexdigest(),
                        'declarations': sorted(names) if names is not None else 'all statement declarations'})
    result += '''
namespace AKLTPalomar

/-- Theorem 1.2 (`t:main`, `sec1-result.tex`): all-period uniqueness and an eventual uniform gap. -/
def Main : Prop := AKLT.Challenge.MainStatementV2

/-- The unconditional theorem, Theorem 1.2 (`t:main`, `sec1-result.tex`). -/
theorem aklt_gap : Main := by
  sorry

end AKLTPalomar
'''
    assert len(result.splitlines()) <= 1000
    assert len(result.encode()) <= 100 * 1024
    return result.encode(), (json.dumps(sources, indent=2) + '\n').encode()


def main():
    root = Path(__file__).resolve().parents[1]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--tree', type=Path, default=root)
    parser.add_argument('--output', type=Path, default=root)
    parser.add_argument('--check', action='store_true', help='Fail on any byte difference; never rewrite files')
    args = parser.parse_args()
    challenge, sources = render(args.tree)
    generated = {'Challenge.lean': challenge, 'statement-sources.json': sources}
    if args.check:
        bad = [name for name, data in generated.items()
               if not (args.output/name).is_file() or (args.output/name).read_bytes() != data]
        if bad:
            raise SystemExit('Generated statement is stale: ' + ', '.join(bad))
        print('PASS: Challenge.lean and statement-sources.json are byte-for-byte reproducible')
    else:
        args.output.mkdir(parents=True, exist_ok=True)
        for name, data in generated.items():
            (args.output/name).write_bytes(data)
        print(f'Challenge: {len(challenge.splitlines())} physical lines, {len(challenge)} bytes')


if __name__ == '__main__':
    main()
