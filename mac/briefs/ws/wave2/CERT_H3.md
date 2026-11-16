# CERT_H3 — design and prototype the kernel check of the stationary (H3′) certificates

**Targets (finite data statements).** `AKLT.Blueprint.Top.Automaton10Statement` and
`AKLT.Blueprint.Top.StationaryCheckStatement` (definitions in `AKLT/Defs/Automaton.lean`, `AKLT/Defs/Stationary.lean`,
`AKLT/Defs/Kernel.lean`, `AKLT/Defs/Computational.lean`; plan statements `p:automaton10`, `d:stationary-certificate`,
`d:prefix-bound`, `p:stationary-check` in `/home/ubuntu/aklt/reports/REV-PLAN/PLAN.md`). Directory `AKLT/Cert/H3/`.

**Material.** The five stationary potentials and verifiers: `/home/ubuntu/aklt/compfeas/` (report.md H3′ sections;
`data/stationary_{B,C}_m10_R70_d*_coarse.bin.gz`, format in the report; `experiments/check_stationary_integer.c`,
`exact_stationary_prefix.py`, `minimize_windows.py`). Measured kernel behaviour:
`/home/ubuntu/aklt/reports/PROBE2/report.md` (packed guard rows ≈ 0.7 ms/row; literal loading via a balanced
elaborator ≈ 1.55 s/MB, ≥ 50 MB per module works; long single reductions retain memory, so shard; prefix
enumeration needs frontier sharding) and its probe sources in `/home/ubuntu/aklt/wt/PROBE2/AKLT/Probe2/`. Proved
generic libraries: `AKLT/Gen/Packed` (lane arithmetic, guarded comparison), `AKLT/Gen/Bellman` (scaled row checks,
local-to-global).

**Deliver.** (1) A design: the exact Lean form of the data (plane literals per module, masks, indexing), the
packed Bellman-row checker for real rows (routing, caps, centre/target/boundary exceptions, known initial-bond
rules), the automaton regeneration/quotient check, the weighted exact-prefix check with frontier sharding and a
verified endpoint table, and how each Boolean check implies the Defs statements (soundness lemmas, stated as closed
Props with proofs where short). (2) A working PROTOTYPE, kernel-checked end to end from the Defs: the memory-10
automaton quotient check (or a measured shard of it), one data module with real planes of one case, real Bellman
rows for at least 64 rows of that case, and one real prefix shard — with measured time/RSS. (3) An exporter
(Python) that writes the Lean data modules from the archived potentials. (4) A production plan: number of
modules, CPU-hours, disk, the build order, and `leaves.json` (open soundness lemmas and check modules) for the
writers. Certificate modules (data and check modules under `AKLT/Cert/H3/Data/` and `AKLT/Cert/H3/Check/`) may use
`set_option maxHeartbeats 0`/`maxRecDepth`. Disk budget 60 GB under your worktree and
`/home/ubuntu/aklt/scratch/CERT_H3/`; abort if free disk on `/` falls below 100 GB. Up to 12 Lean processes and
160 GB RAM. Worktree `/home/ubuntu/aklt/wt/CERT_H3`; report `/home/ubuntu/aklt/reports/CERT_H3/report.md`
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
