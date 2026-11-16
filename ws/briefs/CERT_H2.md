# CERT_H2 — prove the (H2) input outright in Lean

**Target.** Prove `AKLT.Blueprint.Top.H2Statement` (= `OpenTrailBound 10 certifiedRate`) with no hypotheses, by
proving `ALMStatement`, `H2DihedralStatement` (or bypass the dihedral reduction by checking all 916 raw memory-6
windows, if you then prove what the downstream statements need — say exactly which Top statements you prove and
which become unnecessary), `H2TestStatement` and `H2CVStatement` (all in `AKLT/Blueprint/Top/Computation.lean`;
definitions in `AKLT/Defs/Trails.lean`, `AKLT/Defs/Computational.lean`). Directory `AKLT/Cert/H2/`.

**Material.** Plan statements `d:memory-automaton`, `d:memorygrowth`, `l:alm`, `l:H2-dihedral`, `p:H2-test`,
`l:H2-CV`, `h:H2` in `/home/ubuntu/aklt/reports/REV-PLAN/PLAN.md`; paper text
`/home/ubuntu/aklt/reports/REV_C2/app-input-contracts.tex` if present; the exact rational witness and checker in
`/home/ubuntu/aklt/compfeas/` (`data/h2_fifth_m6k1_vector.txt`, `experiments/exact_h2.py`, report H2 sections); a
kernel-checked probe of the complete finite test that already passes (18 s, 9 GB):
`/home/ubuntu/aklt/wt/PROBE2/AKLT/Probe2/H2Small.lean`; the generic growth lemma in `AKLT/Gen/Bellman/Growth.lean`.
The kernel check module may use `set_option maxHeartbeats 0` and `maxRecDepth` (it is a certificate module; name
it `AKLT/Cert/H2/Check.lean`). Worktree `/home/ubuntu/aklt/wt/CERT_H2`; report
`/home/ubuntu/aklt/reports/CERT_H2/report.md`. Report first line `STATUS: PROVED | PROVED FROM DEPS | PARTIAL | FALSE`.

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
