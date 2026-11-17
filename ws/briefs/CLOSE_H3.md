# CLOSE_H3 — make the two H3′ certificate statements unconditional

**Context.** `/home/ubuntu/aklt/repo` (branch `main`) is a Lean 4 formalization; `AKLT.Final.main_of_certificates`
(module `AKLT.Final.Conditional`) proves the headline from four finite certificate statements, two of them for
the input (H3′): `AKLT.Blueprint.Top.Automaton10StatementV2` and `AKLT.Blueprint.Top.StationaryCheckStatementV2`.
The H3′ certificate lane has finished its numerical production: worktree `/home/ubuntu/aklt/wt/CERT_H3`
(READ-ONLY for you; another task is running there) holds all 5,035 generated modules with retained oleans
(31.6 GB, opt-in Lake library `CertData`), the hand-written kernel/bridge layer (`CertData/H3/**`, merged on
`main`), and generated assemblies that are kernel-checked conditional on 56 closed leaf Props. Report:
`/home/ubuntu/aklt/reports/CERT_H3/report.md` (sections on phase 3: merge set, production, how generated modules
attach, "CertData.H3.Bridge.All.stationary_from_leaves"); leaf list
`/home/ubuntu/aklt/reports/CERT_H3/leaves-open.json`. Every one of those 56 leaves now has a merged proof on
`main`: leaf number NNN of `leaves-open.json` (1-based, file order) is `AKLT.W.H3CNNN.main` in module
`AKLT.W.H3CNNN.Main` (exact map: `/home/ubuntu/aklt/state/lw/leaves.json`, keys `H3C001`…`H3C056`, fields `node`,
`module`).

**Task.** Deliver named, kernel-checked, hypothesis-free proofs of those two Top statements, of exactly their
types as they stand on `main`, by composing the generated assemblies (reuse the retained oleans; do NOT re-run the
numerical production), the hand-written assemblies and the merged leaf theorems. Work in
`/home/ubuntu/aklt/wt/CLOSE_H3` (your worktree: a checkout of current `main`, built for the ordinary `AKLT`
library). Attach the generated library by copying or hard-linking the needed sources/oleans from the lane's
worktree into yours as its report describes (check that the hand-written sources the generated oleans were built
against are byte-identical to those on `main`; if an interface drifted, repair the hand-written bridge in your
worktree, never the statements, and say exactly what drifted). Put the closing module(s) under
`CertData/H3/Close/` in the opt-in certificate library (not in the default `AKLT` target). Verify: exact types by
`example`, `#print axioms` (only propext, Classical.choice, Quot.sound), no `sorry`, and that nothing is left as a
hypothesis. If a merged leaf proof does not fit an assembly (type mismatch), report the exact mismatch instead of
working around it. One known hazard, for information: `AKLT.W.H3C026.deadMask_proved` is slow in the independent
checker con-ron; that does not concern this task (Lean's kernel accepts it).
Report `/home/ubuntu/aklt/reports/CLOSE_H3/report.md`, first line `STATUS: COMPLETE | PARTIAL (reason)`: the fully
qualified names and modules of the two proofs, the exact build command from a state where the generated oleans are
attached, time and peak memory of that build, disk used, and what a clean re-build from sources would cost.
Up to 8 Lean processes, 120 GB RAM, 60 GB disk.

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
