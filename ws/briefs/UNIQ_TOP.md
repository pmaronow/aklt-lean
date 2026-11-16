# UNIQ_TOP — prove the interface statement TorusKernelStatement from the proved uniqueness development

**Target.** Prove `AKLT.Blueprint.Top.TorusKernelStatement` (in `AKLT/Blueprint/Top/Quantum.lean`; plan label
`p:toruskernel` in `/home/ubuntu/aklt/reports/REV-PLAN/PLAN.md`; paper text
`/home/ubuntu/aklt/reports/REV_A1/sec3-quantum-frames.tex`) as a theorem
`AKLT.W.UNIQ_TOP.torusKernel : AKLT.Blueprint.Top.TorusKernelStatement` in directory `AKLT/W/UNIQ_TOP/`.
The development `AKLT/Uniq/` in your worktree already proves `AKLT.Uniq.uniqueness` (B ≠ 0 and
ker H = span{B} for every size) together with its supporting lemmas (edge lemma, divisibility, bond algebra): reuse
them; prove whatever further conjuncts the Top statement has from those lemmas or directly. If a conjunct is false
or not provable as stated, say so precisely with the reason (status FALSE or PARTIAL) and state what is provable.
Worktree `/home/ubuntu/aklt/wt/UNIQ_TOP`; report `/home/ubuntu/aklt/reports/UNIQ_TOP/report.md`, first line
`STATUS: PROVED | PROVED FROM DEPS | PARTIAL | FALSE`. Up to 4 Lean processes.

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
