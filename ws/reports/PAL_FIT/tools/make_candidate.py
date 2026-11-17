#!/usr/bin/env python3
"""Generate a four-premise conditional theorem from the frozen closing contract.
No existing project source is modified. Data libraries and their files are excluded.
"""
import hashlib
import json
from pathlib import Path
import shutil

ROOT = Path('/home/ubuntu/aklt/wt/PAL_FIT')
REPORT = Path('/home/ubuntu/aklt/reports/PAL_FIT')
x = json.loads((REPORT / 'hypotheses.json').read_text())
hypotheses = x['hypotheses']
certs = [r for r in hypotheses if r['kind'] == 'certificate']
leaves = [r for r in hypotheses if r['kind'] != 'certificate']
assert len(certs) == 4 and len(leaves) == 416 and all(r['proof'] for r in leaves)
base = ROOT / 'AKLT/PALFit'
base.mkdir(exist_ok=True)
statement = '\n'.join([
 'module',
 'public import AKLT.Blueprint.Top.Operator',
 'public import AKLT.Blueprint.Top.ComputationV2',
 'public import AKLT.Challenge.MainV2', '',
 '@[expose] public section', 'namespace AKLT.PALFit', '',
 '/-- Explicit remaining certificate obligations, in closing-contract order. -/',
 'def ConditionalMainStatement : Prop :=',
 *(f"  {r['lean_name']} →" for r in certs),
 '  AKLT.Challenge.MainStatementV2', '', 'end AKLT.PALFit', ''
])
solution = '\n'.join([
 'module', 'public import AKLT.PALFit.Statement',
 'public import AKLT.Final.Skeleton',
 *(f"public import {module}" for module in sorted({r['proof']['module'] for r in leaves})),
 '', '@[expose] public section', 'set_option backward.proofsInPublic true',
 'namespace AKLT.PALFit', '',
 '/-- The all-parity headline conditional on exactly the four finite contracts. -/',
 'theorem conditionalMain',
 *(f"    ({r['parameter']} : {r['lean_name']})" for r in certs),
 '    : AKLT.Challenge.MainStatementV2 := by',
 '  exact AKLT.Final.mainV2_of_open',
 *(f"    ({r['parameter'] if r['kind'] == 'certificate' else r['proof']['term']})" for r in hypotheses),
 '', '#print axioms conditionalMain', 'end AKLT.PALFit', ''
])
challenge = '\n'.join([
 'module', 'public import AKLT.PALFit.Statement', '',
 '/- The statement is the def AKLT.PALFit.ConditionalMainStatement.',
 '   A standard theorem placeholder is pending resolution of the campaign',
 '   ban on proof holes; this file currently contains no theorem target. -/', ''
])
audit = '\n'.join([
 'module', 'import AKLT.PALFit.Solution', '',
 '#check AKLT.PALFit.conditionalMain',
 '#print axioms AKLT.PALFit.conditionalMain',
 '#print axioms AKLT.Final.mainV2_of_open',
 *(f"#print axioms {r['proof']['term']}" for r in leaves), ''
])
for name, text in [('Statement', statement), ('Solution', solution), ('Challenge', challenge), ('Audit', audit)]:
 # The header-only attempt failed: a module cannot import the legacy tree.
 # The port is intentionally a separate overlay/pilot, never a whole-tree edit.
 text=text.removeprefix('module\n').replace('public import ','import ').replace('@[expose] public section\n','')
 text=text.replace('four finite contracts','four certificate contracts')
 (base / f'{name}.lean').write_text(text)
config = {'challenge_module': 'AKLT.PALFit.Challenge',
          'solution_module': 'AKLT.PALFit.Solution',
          'theorem_names': ['AKLT.PALFit.conditionalMain'],
          'permitted_axioms': ['propext', 'Quot.sound', 'Classical.choice']}
(base / 'comparator.json').write_text(json.dumps(config, indent=2) + '\n')
candidate = REPORT / 'candidate'
candidate.mkdir(exist_ok=True)
# Fresh source-only ordinary tree, deliberately no generated CertData library.
shutil.copytree(ROOT / 'AKLT', candidate / 'AKLT', dirs_exist_ok=True,
                ignore=shutil.ignore_patterns('__pycache__', '*.pyc'))
shutil.copytree(ROOT / 'CertData',candidate / 'CertData',dirs_exist_ok=True,
                ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
for name in ['AKLT.lean', 'lean-toolchain', 'lake-manifest.json']:
 shutil.copy2(ROOT / name, candidate / name)
shutil.copy2(ROOT/'CertData.lean',candidate/'CertData.lean')
(candidate / 'lakefile.toml').write_text('''name = "aklt_lean"
version = "0.1.0"
defaultTargets = ["AKLT"]

[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4.git"
rev = "065356127b1dc0016f66b7283ce0ce2c4055aa55"

[[lean_lib]]
name = "AKLT"
globs = ["AKLT", "AKLT.+"]
leanOptions = { autoImplicit = false, relaxedAutoImplicit = false }

[[lean_lib]]
name = "CertData"
globs = ["CertData", "CertData.+"]
leanOptions = { autoImplicit = false, relaxedAutoImplicit = false }
''')
(candidate / 'comparator.json').write_text(json.dumps(config, indent=2) + '\n')
manifest = {str(p.relative_to(candidate)): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in sorted(candidate.rglob('*.lean'))}
(REPORT / 'candidate-sources.json').write_text(json.dumps(manifest, indent=2) + '\n')
print('candidate:', candidate, 'Lean files:', len(manifest))
print('additional leaf premises: none')
