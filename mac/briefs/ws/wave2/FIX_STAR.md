# FIX_STAR — make two proved leaves acceptable to the independent checkers

**Context.** Worktree `/home/ubuntu/aklt/wt/FIX_STAR` (branch from `main`, built). Two leaf proofs compile with
Lean and have the right types and axioms:
- `AKLT.W.Q037.main : AKLT.Blueprint.Q.StarCasimirChartStatement` (`AKLT/W/Q037/Main.lean`)
- `AKLT.W.Q038.main : AKLT.Blueprint.Q.StarProjectorTransportStatement` (`AKLT/W/Q038/Main.lean`)

The release also requires every declaration to be accepted by two independent kernel re-checkers run on the exported
environment, `con-ron --verified` and NanoDa. On these two modules `con-ron` does not terminate in reasonable
memory: all but a handful of declarations are checked in seconds, and then resident memory grows by about 25 GB per
minute without end (the full-tree run died at ~500 GB). Lean's own kernel accepts the same terms quickly, so some
declaration relies on a reduction that Lean's kernel shortcuts (lazy unfolding, caching, special support) and the
simpler checker does not — typically a proof closed by `rfl`/`decide`/`simp` that makes the kernel decide a
definitional equality between large unfolded terms (equivalences built with `Equiv.ofBijective`, `Fintype`/`Finset`
computations, `fin_cases` over product types, `PiLp` isometries unfolded through instances, casts, etc.).

**Tool.** `/home/ubuntu/aklt/bin/conron-check.sh WT OUT MODULE…` exports the public declarations of the given
modules with their dependency closure from worktree WT and runs both checkers; con-ron is killed when it passes
`CAP_GB` (default 24) of resident memory; `OUT/progress.log` has one `con-ron: check i/N <kind> <name>` line per
FINISHED check, so the declarations of your module missing from it are the ones that do not finish. Example:
`CAP_GB=24 /home/ubuntu/aklt/bin/conron-check.sh /home/ubuntu/aklt/wt/FIX_STAR /home/ubuntu/aklt/reports/FIX_STAR/chk1 AKLT.W.Q038.Main`
(success prints `BOTH CHECKERS ACCEPT`). You can check a smaller module of your own in the same way to bisect.

**Deliver.** Rewrite the offending declarations (only files under `AKLT/W/Q037/` and `AKLT/W/Q038/`; new helper
files there are fine) so that:
1. the two theorems above keep exactly their names and types, and still compile with only the axioms
   propext, Classical.choice, Quot.sound;
2. `conron-check.sh` prints `BOTH CHECKERS ACCEPT` for `AKLT.W.Q037.Main` and for `AKLT.W.Q038.Main`, with con-ron
   peak memory below 8 GB and a few minutes at most each.
Find the exact offending declarations first (bisect with the tool), say in the report what construct caused it, and
replace it by an argument that does not ask the kernel for a large definitional unfolding (state the equality as a
lemma proved by `ext`/rewriting with explicit lemmas, avoid `rfl`/`decide` through `Equiv.ofBijective` and through
`Fintype` instances, use `simp only` with named lemmas, split big `fin_cases` products into lemmas, etc.).
If the two leaves share the cause, fix both the same way. Do not change any file outside those two directories.

Report `/home/ubuntu/aklt/reports/FIX_STAR/report.md`, first line `STATUS: COMPLETE | PARTIAL (reason)`: the
offending declarations and construct, what you changed, the final tool output lines for both modules (peak memory,
times), `#print axioms` for both theorems, and one paragraph "rule for writers" (what proof patterns to avoid so
that con-ron stays cheap) — it will be added to the writers' common brief. Up to 4 Lean processes; keep any single
checker run under 30 GB (the tool enforces the cap you pass).

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
