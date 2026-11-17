# PAL_FIT — does the formalization fit Palomar's verifier, and what must change

**Context.** `/home/ubuntu/aklt/repo` (branch `main`) is a Lean 4 formalization with headline
`AKLT.Challenge.MainStatementV2`. The proof tree (about 95,000 declarations in the export) is nearly complete;
`AKLT.Final.mainV2_of_open` derives the headline from the leaf statements and four finite certificate statements.
Those certificate statements are discharged by generated modules in opt-in Lake libraries: H3′ (5,035 modules,
about 20 CPU-hours of Lean kernel time, 31.6 GB of oleans, some modules needing up to 15 GiB) and H1 (7,964
modules, forecast about 115 CPU-hours, per-module caps 9–11 GiB, two at 64 GiB). Reports:
`/home/ubuntu/aklt/reports/CERT_H3/report.md`, `/home/ubuntu/aklt/reports/CERT_H1/report.md`, and measured
independent-checker timings on samples in `/home/ubuntu/aklt/reports/REL_FEAS/report.md` (use them; do not repeat
those measurements). Earlier Palomar packages of the same author, for the packaging conventions:
`/home/ubuntu/dbl/sources/own/slowequilibration-palomar` (read-only; `scripts/verify*.py`, `comparator.json`,
`verification/README.md`).

**Palomar production limits (from the official verifier checkout
`/home/ubuntu/dbl/scratch/PAL-DRY/tools/PalomarSubmission`: `README.md`, `verification-profile.json`,
`execution-profiles.json`, `docs/launch-security-review.md` — read them; treat that checkout as read-only).**
- Default profile `palomar-namespace-16x32-v1`: 16 CPU, 32 GiB RAM. Approved larger profile
  `palomar-namespace-32x64-v1`: 32 CPU, 64 GiB, same time budget, granted only after a validated OOM/timeout.
- One execution budget of 19,800 s (5.5 h; job timeout 350 min) covers setup, fetching the pinned Mathlib cache,
  a clean build of the entire submitted repository from sources (fresh `.lake`), the Comparator (statement
  comparison; Lean's kernel and NanoDa must BOTH accept the full export of the Solution), and a con-ron replay of
  that export (30-minute cap; an authenticated capacity limit leaves it inconclusive rather than rejecting).
- Memory pressure/ceiling at 95%/98% of the host; at least 20 GB free workspace.
- Every `.lean` file in the submitted repository — generated certificates included — must use Lean's module
  system (`module` header) and have at most 10,000 physical lines; Challenge files at most 1,000 lines / 100 KiB.

**Question.** Under those limits the certificate modules as built are over budget by an order of magnitude.
Establish exactly what fits and what must change. Work in `/home/ubuntu/aklt/wt/PAL_FIT` (your worktree, a
checkout of `main`, built). The machine is shared with a long production job: use at most 16 CPUs and 32 GiB for
anything you run, and run every timing INSIDE a resource limit equal to Palomar's default profile (e.g.
`systemd-run --user --scope -p CPUQuota=1600% -p MemoryMax=32G -p MemorySwapMax=0`, or cgroup/taskset
equivalents — verify the limit is really enforced and say how).

**Deliver.**
1. CORE DRY RUN. Build a certificate-free candidate package in your worktree (do not touch `main`): Challenge =
   the headline statement with the four finite certificate statements as explicit premises (the natural
   conditional theorem; take the exact premises from `AKLT.Final.mainV2_of_open`'s certificate hypotheses, and the
   leaf proofs currently on `main`; where a leaf is not yet proved keep it as a further named premise and list
   it), Solution, `comparator.json`. Run the official verifier's stages on it under the 16 CPU / 32 GiB limit as
   far as they can run today (source checks, clean build with fresh `.lake` and the Mathlib cache, Audit,
   Comparator with Lean + NanoDa, con-ron replay) and report wall time, CPU time and peak memory per stage, and
   every rule the tree violates (module system, line caps, anything else the official source checks report).
   Known hazards to check: two declarations are slow for con-ron (`AKLT.Cert.H2.complete_checked` ~8 min,
   `AKLT.W.H3C026.deadMask_proved` > 20 min with growing memory) — measure them in Lean, NanoDa and con-ron.
2. MODULE-SYSTEM PORT. Size the port of the whole tree (1,104 files, 25 already ported) to Lean's module system
   as Palomar requires: what breaks, a mechanical procedure (script) with a pilot on one part directory that
   builds, and an effort estimate. Do not port the whole tree.
3. BUDGET MODEL. A table: for the default and the larger profile, how many CPU-hours of Lean kernel work, how much
   memory per process, and how many GB of export the certificates may cost in total so that setup + clean build +
   Lean replay + NanoDa + con-ron fit in 19,800 s — using the measured core numbers from item 1 and the measured
   checker/Lean ratios in REL_FEAS (state which replays are parallel and which are serial; measure this for the
   Comparator's Lean replay and NanoDa if it is not documented). State the required reduction factor for H1 and
   for H3′ separately, for time, memory and export size.
4. OPTIONS, ranked, each with what it establishes and its risk: (a) conditional Palomar headline with explicit
   certificate premises plus externally verified certificates with receipts; (b) redesigned certificates that fit
   (say what kind of redesign could plausibly reach the factor in item 3 — you are not asked to do it, only to
   judge plausibility from the cost breakdowns in the two lane reports: which stages dominate, what is
   duplicated, what could be shared or proved symbolically); (c) what a request to Palomar for the larger or a
   longer profile would have to ask for, in numbers.
Report `/home/ubuntu/aklt/reports/PAL_FIT/report.md`, first line `STATUS: COMPLETE | PARTIAL (reason)`; write
item 1's measurements as soon as you have them; end with an ORCH-SUMMARY (≤ 25 lines).

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
