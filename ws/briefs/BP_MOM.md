# BP_MOM — Lean blueprint for one part of the AKLT gap proof

**Your directory:** `AKLT/Blueprint/Mom/` (namespace follows it). **Your targets (in `AKLT/Blueprint/Top/`):** MomentsStatement, FiniteFactsStatement, ThreeFactorMeanStatement, ExactStatement.
**Paper text of your part:** /home/ubuntu/aklt/reports/REV_C1a/sec2-moments.tex.
Worktree `/home/ubuntu/aklt/wt/BP_MOM`; report `/home/ubuntu/aklt/reports/BP_MOM/report.md`. Up to 4 Lean processes.

## Blueprint architect brief (common part)

**Context.** We formalize to Palomar standards (kernel-checked, no hypotheses) the streamlined proof that the
spin-2 AKLT Hamiltonian on the square-lattice torus has a unique ground state (all L, N ≥ 3) and a uniform gap (all
L, N ≥ L₀). The statement layer is in your worktree: `AKLT/Challenge/` (frozen headline), `AKLT/Defs/` (shared
definitions) and `AKLT/Blueprint/Top/` (one closed `…Statement : Prop` per interface result, with the proved top
assembly `mainV2_of_parts`). The revision plan with the exact LaTeX statements is
`/home/ubuntu/aklt/reports/REV-PLAN/PLAN.md` (labels in the Top docstrings). Generic proved libraries:
`AKLT/Gen/Bellman`, `AKLT/Gen/Gram`, `AKLT/Gen/Packed`; vendored donors `AKLT/Vendor/` with the reuse map
`/home/ubuntu/aklt/reports/VENDOR_1/reuse-map.md`. The statement layer is under fidelity review in parallel: if
you find a Top or Defs declaration that is false, unprovable as stated, ill-typed for its purpose, or different
from the paper, do NOT edit it — report it precisely (with a counterexample or the paper text) and propose a
`…V2` replacement in your own directory, then build on your V2.

**Your job is the blueprint of your part, not the proofs.** Deliver, in your directory:
1. `Nodes*.lean`: closed leaf statements `def <Name>Statement : Prop` covering every step of the paper proof of your
   targets, each small enough for one writer (≤ ~400 lines of Lean proof, 1–2 hours); split hard steps a second
   time; give each a docstring with the paper label/line and the idea of the proof. Add definitions you need.
2. `Assembly.lean`: PROVED theorems deriving each of your target Top statements from your leaf statements (and
   from other parts' Top statements where the paper uses them) — every hypothesis a closed Prop.
3. Proofs of leaves that are immediate (a few lines); leave the rest open.
4. `leaves.json` in your report directory: for each open leaf: Lean name, module, paper label, difficulty
   (easy/medium/hard), dependencies (other leaves it may use as hypotheses are NOT allowed — leaves are closed;
   list instead the definitions and library lemmas it needs), and a suggested proof route with donor/reuse pointers.
5. A trap check of every leaf: missing premises (the conclusion must follow from the hypotheses stated IN the leaf),
   vacuity, empty/degenerate cases, coercions, `Finset` vs `Fintype` sums, `ℕ` subtraction, division by zero,
   instance arguments silently dropped.
Report first line `STATUS: COMPLETE | PARTIAL (reason)`, then the node table (leaf → paper label → difficulty),
`#print axioms` of every assembly theorem, the list of Top/Defs problems found, and the ORCH-SUMMARY.

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
