# GEN-PACKED — generic Lean library: packed-Nat lane arithmetic with proved semantics

**Goal.** A reusable Lean library (namespace `AKLT.Gen.Packed`, directory `AKLT/Gen/Packed/`) for checking very large
families of nonnegative integer inequalities inside the kernel using a few GMP-accelerated `Nat` operations on
packed planes P = Σ_s u_s 2^{b s}. It will be used to check a stationary Bellman supersolution certificate (about
3·10⁸ integer values per case) for an (H3′) input. Read the H3′ sections and the "Ranked workstation probe plan" of
`/home/ubuntu/aklt/compfeas/report.md` and the probe files `/home/ubuntu/aklt/compfeas/probes/{Packed*,BellmanGuard*}.lean`.

**Deliver** proved definitions and lemmas: `lane P b s` extraction; packing from a list; lane-wise addition and
multiplication by a scalar without carries under explicit per-lane bounds (no-carry lemmas); shifts/masks as lane
moves (spatial translation on a square grid with zero fill, row/column boundary masks); guarded componentwise
comparison (`Nat.land (guard + B − A) guardMask = guardMask ↔ ∀ s, A_s ≤ B_s` under lane bounds); and a worked
end-to-end example: prove `∀ s, A_s ≤ c₁ B_{s+1} + c₂ B_s` for two literal planes of ≥ 10⁴ lanes by one `decide
+kernel` call plus the semantic lemmas, with `#print axioms`. Measure kernel time/RSS for plane widths 10⁵, 10⁶,
2·10⁶ bits and for 1, 10, 100 rows of such checks in one module; also measure how large a literal `Nat` (hex
literal) a single module can hold before elaboration/olean size becomes the bottleneck (try 1 MB, 10 MB, 50 MB of
packed data). A separate agent (PROBE2) is timing the feasibility study's raw probes; do not repeat its runs — your
job is the proved library and its scaling. Worktree `/home/ubuntu/aklt/wt/GEN-PACKED`; report
`/home/ubuntu/aklt/reports/GEN-PACKED/report.md`. Up to 8 Lean processes and 128 GB RAM.

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
