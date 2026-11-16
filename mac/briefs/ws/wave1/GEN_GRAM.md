# GEN-GRAM — generic Lean library: division-free Gram/residual positivity certificates

**Goal.** A reusable, kernel-efficient Lean library (namespace `AKLT.Gen.Gram`, directory `AKLT/Gen/Gram/`) that
proves positive definiteness of explicit integer symmetric matrices from a supplied witness, for the (H1) part of a
computer-assisted proof. Witness format (from the campaign plan): positive integers g, d, S and an integer
lower-triangular L such that E = d·S²·M − g·L·Lᵀ is strictly diagonally dominant with positive diagonal (L may be
zero when M itself is strictly diagonally dominant). Read the plan's statements `l:gram-residual`,
`l:integercheck`, `p:certificate` in `/home/ubuntu/aklt/reports/REV-PLAN/PLAN.md` (search those labels) and the H1
section of `/home/ubuntu/aklt/compfeas/report.md`; a sample 131-dim certificate is in
`/home/ubuntu/aklt/compfeas/probes/H1Gram.lean` and `/home/ubuntu/aklt/compfeas/data/h1_chol_*.json`.

**Deliver:** (1) Mathlib-level theorem: strictly diagonally dominant real symmetric matrix with positive diagonal is
positive definite (check whether Mathlib already has it — e.g. Gershgorin / `Matrix.PosDef` lemmas — and reuse);
(2) the Gram/residual lemma: if E = d S² M − g L Lᵀ is s.d.d. with positive diagonal and g,d,S > 0 then M is
positive definite (over ℚ and over ℝ/ℂ as Hermitian, whichever the plan's statement needs — provide both if cheap);
(3) an executable Boolean checker on list-of-lists integer matrices (row-wise, structural recursion, `decide
+kernel`-friendly) with a soundness theorem `checker M L g d S = true → (toMatrix M).PosDef`; (4) the measured
kernel cost on the 131-dimensional sample and on the largest (179-dim) block if a witness for it is available in
`/home/ubuntu/aklt/compfeas/data/` (if not, generate a random s.d.d. test of size 179 yourself and say so).
Worktree: `/home/ubuntu/aklt/wt/GEN_GRAM`; report `/home/ubuntu/aklt/reports/GEN_GRAM/report.md`.

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
