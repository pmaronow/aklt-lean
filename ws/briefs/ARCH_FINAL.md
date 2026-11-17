# ARCH_FINAL — the closing assembly and interface audit

**Context.** Repository worktree `/home/ubuntu/aklt/wt/ARCH_FINAL` (branch from `main`): headline
`AKLT.Challenge.MainStatementV2`; statement layer `AKLT/Defs`, `AKLT/Blueprint/Top` (with `mainV2_of_parts`,
`mainV2_of_partsV2`, `InputsStatementV2`); seven part blueprints `AKLT/Blueprint/{Q,Gap,Win,Mom,Rec,H3,H1}` with
their `Assembly.lean` / `AssemblyV2.lean`; proved developments `AKLT/Uniq`, `AKLT/W/UNIQ_TOP` (TorusKernelStatement),
`AKLT/Cert/H2` (H2); leaf proofs arrive continuously as `AKLT/W/<KEY>/Main.lean` (theorem `AKLT.W.<KEY>.main`
of exactly the leaf's type; the map key → leaf is `/home/ubuntu/aklt/state/lw/leaves.json`). The finite
certificate statements for (H1) and (H3′) (`…FiniteData…V2`, `StationaryCheck…V2`, `Automaton10…V2`,
`CertificateStatementV2`, …) are being discharged separately.

**Deliver** in `AKLT/Final/`:
1. `Skeleton.lean`: ONE proved theorem
   `mainV2_of_open : <explicit list of closed Props> → AKLT.Challenge.MainStatementV2`
   whose hypotheses are exactly (a) every non-superseded leaf statement of the seven blueprints and (b) the finite
   certificate statements — nothing else: every interface between parts must be discharged inside the proof by the
   parts' assembly theorems and the already-proved results (uniqueness, TorusKernel, H2). If two parts do not
   compose (a mismatch between what one assembly proves and what another consumes), do not hide it: add the
   missing bridge as a clearly named closed Prop `Bridge_<name>` hypothesis, and list every bridge in your report
   with the exact reason — these are the interface gaps to fix.
2. `inventory.json` in your report directory: for each hypothesis of `mainV2_of_open`: Lean name, kind
   (leaf / certificate / bridge), owning part, and whether a proof already exists in the tree.
3. A generator script `gen_final.py` that, given the set of proved leaves (reading `state/lw/leaves.json` and the
   tree), writes `AKLT/Final/Main.lean` = `theorem main : MainStatementV2 := mainV2_of_open <proof terms…>` once
   every hypothesis has a proof, and otherwise prints the list of missing ones.
Assemblies and plumbing only; do not prove leaves, bridges or certificate statements. Report
`/home/ubuntu/aklt/reports/ARCH_FINAL/report.md`, first line `STATUS: COMPLETE | PARTIAL (reason)`, with the bridge
list, counts, `#print axioms` of `mainV2_of_open`, and an ORCH-SUMMARY (≤ 25 lines). Up to 4 Lean processes.

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
