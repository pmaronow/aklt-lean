# ARCH_UNIQ — Lean blueprint and proof: uniqueness of the AKLT ground state on every torus L, N ≥ 3

**Target.** In namespace `AKLT.Uniq` (directory `AKLT/Uniq/`), state and prove
`theorem uniqueness : ∀ L N : AKLT.Challenge.Size, AKLT.Challenge.B L N ≠ 0 ∧
  LinearMap.ker (AKLT.Challenge.H L N) = Submodule.span ℂ {AKLT.Challenge.B L N}`
using the frozen definitions of `AKLT/Challenge/Main.lean` (do not edit it). This is the first conjunct of
`MainStatementV2` (`AKLT/Challenge/MainV2.lean` in `/home/ubuntu/aklt/wt/ARCH_0/` — read only).

**Mathematics.** The proof to follow is §3 of the revised paper, written at
`/home/ubuntu/aklt/reports/REV_A1/sec3-quantum-frames.tex` (statements d:poly, l:edge, l:divisibility,
p:toruskernel; it uses only polynomial algebra: the identification of ⊗V with multihomogeneous polynomials of degree
4 per site, the edge lemma ker P_e = q_e · V_(3,3) (via the Cartan multiplication map or Clebsch–Gordan), and
divisibility in a UFD by the pairwise nonassociate bond determinants). The plan statements are in
`/home/ubuntu/aklt/reports/REV-PLAN/PLAN.md` (search those labels). Donor code vendored under `AKLT/Vendor/`
(see `AKLT/Vendor/All.lean`; Physlib sl₂ tensor decomposition and QICLean coherent states may help; reuse map in
`/home/ubuntu/aklt/reports/VENDOR_1/reuse-map.md`).

**Deliverable.** (1) A blueprint: closed `def …Statement : Prop` nodes (each ≤ ~400 lines of expected proof),
with a PROVED assembly `uniqueness_of_nodes`; (2) proofs of as many nodes as you can, in dependency order,
prioritizing the hardest-to-delegate ones; (3) a list of the remaining open nodes with exact statements, so that
other writers can take them. Report first line `STATUS: PROVED | PROVED FROM DEPS | PARTIAL`. Worktree
`/home/ubuntu/aklt/wt/ARCH_UNIQ` (from the validated head, includes `AKLT/Vendor`); report
`/home/ubuntu/aklt/reports/ARCH_UNIQ/report.md`. Up to 4 Lean processes.

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
