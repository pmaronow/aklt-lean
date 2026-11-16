# GEN-BELLMAN — generic Lean theory: automaton path sums, Bellman supersolutions, quotients

**Goal.** Generic, statement-level Lean mathematics (namespace `AKLT.Gen.Bellman`, directory `AKLT/Gen/Bellman/`) for
bounding infinite sums of nonnegative weights over stopped paths of a (countable or finite) labelled transition
system by a supersolution, as used in Appendix C of the campaign plan. Read in
`/home/ubuntu/aklt/reports/REV-PLAN/PLAN.md` the statements `l:automaton-quotient`, `d:stationary-walk`,
`l:Bellman-soundness`, `d:stationary-certificate`, `l:stationary-local-global`, `l:prefix-domination` and
`l:alm` (search the labels), and the H3′ sections of `/home/ubuntu/aklt/compfeas/report.md`.

**Deliver, fully proved, in generic form** (abstract state type, nonnegative real or ENNReal weights, reward at
stopping states): (1) Bellman soundness: if F ≥ 0 satisfies F(x) ≥ r(x) at stopping states and
F(x) ≥ Σ_y w(x,y) F(y) elsewhere, then the total weight of all stopped paths from x (as a tsum or a supremum of
finite-length sums) is ≤ F(x); (2) the finite-to-global extension: a function equal to a free-walk sub-invariant z
outside a finite box, with checked rows inside, is a global supersolution; (3) exact lumping of a labelled
deterministic automaton (a quotient map compatible with transitions and labels transports path sums); (4) the
one-step positive-vector growth lemma (`M h ≤ λ h` entrywise with h > 0 bounds all-length weighted sums by
C λⁿ) in the form `l:alm` needs. Keep statements general (Finset/Fintype or countable with tsum over ENNReal), prove
them, and state precisely what a concrete instance must supply. No data or kernel computation here.
Worktree `/home/ubuntu/aklt/wt/GEN_BELLMAN`; report `/home/ubuntu/aklt/reports/GEN_BELLMAN/report.md`.

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
