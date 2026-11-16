# ARCH_0 — the Lean statement layer: Challenge V2, shared definitions, interface Props, proved top assembly

**Context.** We formalize to Palomar standards the streamlined, strengthened proof described by the revision plan
`/home/ubuntu/aklt/reports/REV-PLAN/PLAN.md` (read it in full, including [AMENDED] items; `interfaces.tex` there has
the interface statements as LaTeX). Proof text for each part is being written in parallel by other agents from the
same plan. The current frozen Challenge is `AKLT/Challenge/Main.lean` in your worktree (Theorem 1.1 for even sizes;
keep its definitions — do not edit it).

**Author decisions (binding).** The headline theorem is now: for ALL L, N ≥ 3, ker H_{L,N} = span{B}; and there
exist c > 0 and L₀ such that for all L, N ≥ L₀ (any parity) every nonzero eigenvalue of H_{L,N} is ≥ c. Constants
existential. NO general-graph ground-space theorem (cut by the author from paper and Lean), no infinite-volume or
thin-torus results.

**Deliver** (directories `AKLT/Challenge/`, `AKLT/Defs/`, `AKLT/Blueprint/Top/` in your worktree):
1. `AKLT/Challenge/MainV2.lean`: imports only Mathlib and `AKLT.Challenge.Main` (reuse its definitions; no new
   physics definitions unless needed), defines `MainStatementV2 : Prop` exactly as above, ≤ 100 lines, readable,
   with docstrings. Deliver this FIRST and write `/home/ubuntu/aklt/reports/ARCH_0/CHALLENGE_V2_READY` (containing
   its sha256) as soon as it compiles, so that fidelity review can start while you continue.
2. `AKLT/Defs/`: the shared Lean definitions of the plan's frozen common definitions (d:model as the Challenge's H,
   d:moment, d:poly, d:frame, d:framemodel, d:shells, d:pinmodel, the domain/trace objects, patterns, kernels, and
   the computational-input statements) — exactly the objects the cross-lane interface statements mention. Design
   them for formalization (finite types, `Fin`, finite sums; no measure theory unless unavoidable).
3. `AKLT/Blueprint/Top/`: one closed `def …Statement : Prop` per cross-lane interface theorem of the plan (at least
   t:inputs, t:rec / h:P, t:cutMOS with d:W, t:mainW, p:toruskernel, t:QD, and any others the assembly needs), each
   with a docstring giving the plan label, and a PROVED assembly theorem
   `mainV2_of_parts : InputsStatement → … → MainStatementV2` (all hypotheses are these closed Props).
4. A report mapping every Lean definition and Prop to the plan label and exact LaTeX statement, with the modelling
   choices, the Lean traps checked, and a list of statements whose Lean form differs from the LaTeX in any way.
Worktree `/home/ubuntu/aklt/wt/ARCH_0`; report `/home/ubuntu/aklt/reports/ARCH_0/report.md`. Up to 6 Lean processes.

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
