#!/usr/bin/env python3
"""Source-only conditional package: exact Solution source closure plus Challenge/Audit."""
import hashlib
import json
from pathlib import Path
import shutil
R=Path('/home/ubuntu/aklt/reports/PAL_FIT')
WT=Path('/home/ubuntu/aklt/wt/PAL_FIT')
OUT=R/'package'
OUT.mkdir(exist_ok=True)
modules=set(json.loads((R/'source-closures.json').read_text())['AKLT.PALFit.Solution'])
modules.update(['AKLT.PALFit.Challenge','AKLT.PALFit.Audit'])
rows=[]
for module in sorted(modules):
 rel=Path(*module.split('.')).with_suffix('.lean')
 target=OUT/rel;target.parent.mkdir(parents=True,exist_ok=True)
 shutil.copyfile(WT/rel,target)
 rows.append(dict(module=module,path=str(rel),bytes=target.stat().st_size,sha256=hashlib.sha256(target.read_bytes()).hexdigest()))
# Preserve upstream license notices for vendored sources retained in the closure.
for license_path in (WT/'AKLT/Vendor').rglob('LICENSE'):
 target=OUT/license_path.relative_to(WT)
 if target.parent.is_dir():shutil.copyfile(license_path,target)
for name in ['lean-toolchain','lake-manifest.json']:
 shutil.copyfile(WT/name,OUT/name)
shutil.copyfile(WT/'AKLT/PALFit/comparator.json',OUT/'comparator.json')
shutil.copyfile(R/'candidate/README.md',OUT/'README.md')
(OUT/'README.md').write_text((OUT/'README.md').read_text().replace(
 'The small handwritten `CertData` interface modules remain because ordinary proofs import them.',
 'It contains the 850-module Solution closure plus Challenge and Audit. Unused handwritten `CertData` support modules are excluded; they are covered separately by the whole-tree audit.'))
(OUT/'lakefile.toml').write_text('''name = "aklt_lean"
version = "0.1.0"
defaultTargets = ["AKLT"]

[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4.git"
rev = "065356127b1dc0016f66b7283ce0ce2c4055aa55"

[[lean_lib]]
name = "AKLT"
roots = ["AKLT.PALFit.Solution", "AKLT.PALFit.Challenge", "AKLT.PALFit.Audit"]
globs = ["AKLT.+"]
leanOptions = { autoImplicit = false, relaxedAutoImplicit = false }
''')
(R/'package-sources.json').write_text(json.dumps(rows,indent=2)+'\n')
print('source-only package',OUT,'Lean files',len(rows),'Lean bytes',sum(r['bytes'] for r in rows))
