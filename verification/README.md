# Verification boundary and records

The current release targets the unconditional `AKLTPalomar.aklt_gap`. Its generated
H1 and H3 certificate sources are pending regeneration against the ported kernels.
The hand-written build, strict available-source axiom audit, and protected
Comparator regression for the two-input theorem are recorded separately. A
conditional regression pass never means the unconditional theorem has completed
its package build or checker replays.

The earlier `local-receipt.json`, `axioms.log`, and `axioms-compat.log` are historical
two-input package records. Their source identity is the earlier package commit
recorded in those files. Current records belong under `verification/full-port/`.
No export or compiled project object is committed. The source manifest is
`PORT-MANIFEST.tsv`; the generated-module inventory is `generated-modules.json`.

Run `scripts/cold-verify.sh` with a package repository and full commit, the official
verifier checkout, and hash-pinned generated-source archives for full verification.
Before regeneration, add `--regression-inputs` and omit the archives. The script
starts from a fresh clone, fetches pinned dependencies and the Mathlib cache,
and never runs `lake update` or builds Mathlib from source. Author-owned metadata
TODOs are recorded and do not hide mechanical failures.

The tools required are Python 3 with pip, Git, curl, a C compiler, pkg-config,
tar, zstd, and ordinary Linux utilities. If needed, the official source-pinned
bubblewrap installer is bootstrapped with pinned Meson/Ninja and extracted
libcap headers. A restricted host may need administrator namespace policy.
The source toolchain must be installed through Elan. Checker downloads are
verified against the official binary digest.

Resource measurements use 16 CPUs' affinity. The runner inherits the caller's
cgroup and records its limits; it does not claim authenticated Palomar capacity
evidence. The author has removed external verifier resource limits from the
release requirements. Configurable local time and memory watchdogs remain.
