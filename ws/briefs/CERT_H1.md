# CERT_H1 — design and prototype the kernel check of the (H1) operator certificates

**Targets (finite data statements).** `AKLT.Blueprint.Top.IntegerCheckStatement` and
`AKLT.Blueprint.Top.CertificateStatement` (definitions in `AKLT/Defs/Pattern.lean`, `AKLT/Defs/Operator.lean`,
`AKLT/Defs/OperatorContracts.lean`; plan statements `d:pattern`, `d:reduction`, `d:Pauli`, `d:exchange`,
`l:integercheck`, `p:certificate` in `/home/ubuntu/aklt/reports/REV-PLAN/PLAN.md`; paper text
`/home/ubuntu/aklt/reports/REV_C3/app-local-operator.tex`). Directory `AKLT/Cert/H1/`.

**Material.** `/home/ubuntu/aklt/compfeas/report.md` (H1 sections: 7,962 patterns, 12,173 exchange-sector blocks
of size ≤ 179, sparse operator construction counts, the Gram/residual witness format, Kronecker-packing and
pairing-diagram ideas) and its code (`experiments/enumerate_patterns.py`, `profile_h1_operator.py`,
`profile_h1_chol*.py`, `h1_dimensions.py`; programs under `programs/h1-local/code/`). A complete saved witness set
is being exported to `/home/ubuntu/aklt/data/h1/` by another agent (README there when ready). Proved library
`AKLT/Gen/Gram` (checker + soundness; a 131-dim block checks in ~108 s / 24 GB as one reduction — shard rows).
Kernel measurements: `/home/ubuntu/aklt/reports/PROBE1/report.md`, `/home/ubuntu/aklt/reports/PROBE2/report.md`.

**Deliver.** (1) A design of the in-kernel constructor: from the pattern record to the integer sector matrices
(moment contraction, inversion mask, Pauli substitution, exchange/weight-sector restriction), in a sparse or packed
representation that the kernel can afford, with the soundness chain to the Defs statements as closed Props (proofs
where short); and of the coverage check (the enumeration of raw pattern configurations is represented by the 7,962
classes at the right thresholds). (2) A working PROTOTYPE, kernel-checked end to end from the Defs for one small
pattern and one of the largest (a 179-dimensional block), with measured time/RSS for constructor and positivity
check separately. (3) An exporter (Python) from the saved witness set to Lean data modules. (4) A production plan
(modules, CPU-hours, memory per module, build order) and `leaves.json` for the writers. Certificate modules under
`AKLT/Cert/H1/Data/` and `AKLT/Cert/H1/Check/` may use `set_option maxHeartbeats 0`/`maxRecDepth`. Disk budget
40 GB; abort if free disk on `/` falls below 100 GB. Up to 12 Lean processes and 160 GB RAM. Worktree
`/home/ubuntu/aklt/wt/CERT_H1`; report `/home/ubuntu/aklt/reports/CERT_H1/report.md`
(first line `STATUS: COMPLETE | PARTIAL (reason)`).

## Rules for all Lean work in this campaign

- **Project:** your worktree is a Lake project (Lean 4.35.0-rc2, Mathlib 065356127b prebuilt and linked). Never run
  `lake update`, never build Mathlib, never touch `.lake/packages`. PATH needs `$HOME/.elan/bin`. Lake here rejects
  `lake build -j`; build single modules (`lake build AKLT.X.Y` or `lake env lean file.lean`). Use at most 4 Lean
  processes at once unless your brief says otherwise; other agents share the machine.
- **Your files:** write only under the namespace directory your brief assigns (e.g. `AKLT/Gen/Gram/`), inside your
  worktree, and in your report directory. Never edit existing files of other directories. Namespaces follow the
  directory (`AKLT.Gen.Gram`).
- **Soundness:** forbidden in delivered files: `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`,
  `extern`, `unsafe`, `opaque`, `macro_rules` redefining tactics, `set_option debug.skipKernelTC`,
  `#eval`/`IO`/`run_cmd` with effects, `maxHeartbeats 0` (except in a certificate module the brief names). Allowed
  axioms: propext, Classical.choice, Quot.sound — check with `#print axioms` on every exported theorem. Unproved
  facts may appear only as `def ... : Prop` statements, never as hypotheses smuggled into theorems you claim proved.
- **Kernel computation (measured on this machine):** use `decide +kernel` with structurally recursive checkers on
  `Nat`/`Int` (GMP-accelerated); lists, not `Array` (list-backed in the kernel); balanced trees for random lookup;
  fixed-denominator dyadics, not `ℚ`, in inner loops; ~4·10⁻⁵ s per elementary step; memory ~48 KB retained per
  cell update — shard big checks into separate modules. A Boolean checker needs a proved soundness theorem.
- **Delivery:** no sub-agents; do not stop before the deliverable exists. Report first line:
  `STATUS: PROVED | PROVED FROM DEPS | PARTIAL | FALSE` (for proof tasks) or `STATUS: COMPLETE | PARTIAL (reason)`
  (for design tasks), then: files, exported declarations with their statements, `#print axioms` output, build
  commands and timings, and open issues.
- **ORCH-SUMMARY:** end your report with a section `ORCH-SUMMARY` of at most 25 lines: what is delivered, what is
  open (exact names), every limitation or deviation, and what the orchestrator must decide or pass on.
