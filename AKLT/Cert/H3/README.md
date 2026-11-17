# H3 finite certificate library

The executable interface is in `CertData/H3/Kernel/Production/Model.lean`,
`Replay.lean`, and `Batching.lean`; the kernel, packed arithmetic, and soundness
layers are hand-written module-system files. Generated literals, checks, and
data-dependent assemblies belong to `CertDataH3` and are excluded from Git.
The unconditional closing module imports `CertData.H3.Bridge.All`.

The production generator and runner use the module system and preserve the
existing 5,032 module names, checker definitions, literal values, and statements.
The six numeric inputs are pinned in `inputs.json`. `H3_INPUT_DIR` can select a
different directory containing those exact inputs. The native export assertions
against the original exact-prefix results are retained in `prefix-reference.json`;
they do not supply Lean proofs. `H3_REPORT_DIR` selects the output receipts
directory. Defaults are `data/h3/` and `verification/runs/H3/` under the repository.

From the release root, with its hand-written module-system dependencies built:

```sh
export PATH="$HOME/.elan/bin:$PATH"
export H3_INPUT_DIR="$PWD/data/H3"
export H3_REPORT_DIR="$(dirname "$PWD")/aklt-verification/H3"
python3 AKLT/Cert/H3/regen.py generate
python3 AKLT/Cert/H3/regen.py build --jobs 16 --ram-gb 160
python3 AKLT/Cert/H3/regen.py close --stage closing --jobs 1
python3 AKLT/Cert/H3/regen.py verify
```

The builder resumes only hash-matching successful kernel checks. `--module`
selects modules and their generated dependency closure; `--force` reruns the
selected modules in fresh processes. Every exported theorem receives a recorded
axiom audit. Resource guards enforce the configured limits, including 40 GB of
available host memory and more than 100 GiB of free disk. No legacy object or
legacy import root is used, and the runner never builds dependencies or Mathlib.

`production.py` is an alternative entry point for the same commands, and
`production_receipts.py` and `production_audit.py` run `verify`. `run_checks.py`
forces selected fresh checks through the same runner. The retained `export.py` and
`generate_prefix.py` are initial prototype generators, outside the production
inventory. The numeric runner preserves the recorded generated inventory and dependency map.

See [the H3 record](../../../docs/regeneration/H3.md) for production measurements, retained artifacts, and the final
assembly interface, [the H3 change note](../../../docs/regeneration/H3-CHANGES.md) for the private sort-body visibility repair,
and [the interface note](../../../docs/REGEN-INTERFACE.md) for the exposed API and cross-module samples.
