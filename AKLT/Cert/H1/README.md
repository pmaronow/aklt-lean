# H1 numeric certificate tooling

The release numeric route is `production_receipts.py inputs`,
`production_reexport.py --install`, `production_build.py`,
`production_receipts.py verify`, and `production_close.py`, all under `tools/`.
It checks 7,964 owner modules and 414,638 generated theorem axiom transcripts.
The source and owner/dependency maps are unchanged by portable path defaults.

`H1_INPUT_DIR` defaults to `data/h1/` under the repository;
`H1_REGEN_REPORT` defaults to `verification/runs/H1/`. `H1_REGEN_ROOT` remains
the independent scratch output override. Explicit `--report-dir` arguments retain
their existing meanings. Every generated proof is checked by the Lean kernel.

See [H1 regeneration](../../../docs/regeneration/H1.md) for exact commands,
input pins, reference per-kind measurements, resource controls, receipts, and
closed contracts. [Tooling notes](../../../docs/regeneration/H1-CHANGES.md)
describe source preservation, and [the shared interface](../../../docs/REGEN-INTERFACE.md)
lists the exposed hand-written kernels. `lake build Handwritten` supplies those
prerequisites; no separate prerequisite script is needed.
