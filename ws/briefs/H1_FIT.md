# H1_FIT — redesign the H1 finite certificate to fit the external verifier (author-directed, top priority)

**Context.** `/home/ubuntu/aklt` holds a Lean 4 formalization of a spectral-gap theorem (paper:
`/home/ubuntu/aklt/manuscript-v2`, the (H1) input is in `sec8-inputs.tex` and `app-input-contracts.tex`; statement
layer on `main` in `/home/ubuntu/aklt/repo`: `AKLT.Blueprint.Top.H1Statement`, `CertificateStatementV2`,
`H1FiniteDataStatementV2`; hand-written checker and soundness layer `AKLT/Cert/H1/**`). The H1 certificate lane
(worktree `/home/ubuntu/aklt/wt/CERT_H1` — READ-ONLY for you, a production run is in progress there; report
`/home/ubuntu/aklt/reports/CERT_H1/report.md`, per-module cost records
`/home/ubuntu/aklt/reports/CERT_H1/phase3/events.jsonl` with `kind`, `user_seconds`, `max_rss_kib`, generators in
`AKLT/Cert/H1/tools/*.py`, witness data `/home/ubuntu/aklt/data/h1/`) verifies an operator bound for 7,962
representative local patterns / 12,173 blocks by a packed constructor of the operator matrices plus a
Gram/residual certificate (E = dS²M − gLLᵀ strictly diagonally dominant): about 115 CPU-hours of Lean kernel
time (constructors ≈ 80 h, local parameters ≈ 15 h, Gram ≈ 8.5 h), 9–11 GiB per module. Earlier feasibility
study with the numerical programs: `/home/ubuntu/aklt/compfeas` and `/home/ubuntu/aklt/reports/COMPFEAS/report.md`.

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

**Target ("the fit").** The whole package — proof tree plus BOTH finite certificates (H1 and H3′) plus H2 — must
pass that verifier on the default profile. The certificates are kernel-checked three times there (clean build;
Lean's kernel replay of the export; NanoDa — measured at 0.1–5x Lean on certificate modules, see
`/home/ubuntu/aklt/reports/REL_FEAS/report.md`), with at most ~5 Lean processes in parallel during the build
(32 GiB) and with the Lean replay possibly serial (being measured). Design to two levels and say which you reach:
- Level A (safe even if the replays are serial): each certificate costs at most ~15 minutes of single-thread Lean
  kernel time in total, at most 4 GiB per process, at most ~200 MB of exported literal data, source files of at
  most 10,000 lines each and a few hundred MB of generated source in total.
- Level B (needs parallel replays or the larger 32 CPU / 64 GiB profile): at most ~3 CPU-hours of Lean kernel
  time per certificate, at most 6 GiB per process, at most ~2 GB of exported literals.
Today: H1 ≈ 115 CPU-hours, H3′ ≈ 20 CPU-hours. Rules that stay: no `native_decide`, no new axioms (only propext,
Classical.choice, Quot.sound), everything kernel-checked; the headline theorem is unchanged (existential
constants: ∃ c > 0, L₀ with every nonzero eigenvalue ≥ c for all L, N ≥ L₀), so ANY valid finite input that makes
the paper's argument go through is acceptable — weaker constants are fine as long as the final inequalities
still close.

**Task.** Find and demonstrate a certificate for (H1) that reaches Level A, or failing that Level B. Be aggressive:
the reduction needed is two orders of magnitude, so tuning is not enough — look for changes of method.
1. ANATOMY (quick, from `events.jsonl` and the generators): where the 115 CPU-hours and the memory go, per kind
   and per cause (operator construction vs arithmetic size vs elaboration/import overhead vs repeated work across
   patterns); what the entry sizes are; what fraction of patterns/blocks is hard.
2. CANDIDATES — consider at least: (i) not constructing the operator in the kernel at all: prove entry formulas
   symbolically once (ladder/moment identities) so that per pattern the kernel only checks a small inequality;
   (ii) a certificate with slack: bound the operator norm by a cruder analytic estimate (Schur test, row sums,
   Gershgorin on a tiny reduced matrix, tensor-product structure, per-site bounds multiplied along the network)
   for most patterns and keep exact certificates only where needed — measure numerically how many patterns need
   them when the required constant is relaxed as far as the rest of the argument allows (the paper's (H2) and
   (H3′) margins and the final contraction say how much H1's constant can be relaxed: read `sec7`/`sec8` and
   quantify the slack); (iii) symmetry and quotient reductions beyond the present representatives (pattern
   classes sharing one matrix, block sizes after full symmetry reduction); (iv) small-integer or fixed-precision
   dyadic arithmetic with rigorous rounding in place of exact big rationals; (v) one shared table of local
   tensors checked once, with per-pattern work reduced to index lookups and one small positive-definiteness
   witness; (vi) replacing the per-pattern statement by a uniform statement over a parameter family proved once.
   For each: expected factor, what must be re-proved in the soundness layer, what must be re-searched
   numerically, risk. Test the promising ones NUMERICALLY first (Python/NumPy/exact rationals outside Lean, in
   your report directory; the existing programs and data are there to reuse) — e.g. how many patterns pass a
   crude bound, how small the witnesses can be made.
3. PILOT the best candidate in Lean on a representative sample (hard and easy patterns): kernel time, memory, and
   independent-checker acceptance/time (`/home/ubuntu/aklt/bin/conron-check.sh` shows how), then extrapolate
   honestly to the full certificate.
4. VERDICT: reaches Level A / Level B / neither, with the full implementation plan (statement changes needed in
   `AKLT/Blueprint/Top` or the paper, soundness leaves to prove, generators to write) and the remaining risk.
Work in `/home/ubuntu/aklt/wt/H1_FIT` (your worktree, a checkout of `main`, built) and
`/home/ubuntu/aklt/reports/H1_FIT`. Up to 8 CPU-heavy processes and 60 GB RAM (the production job has priority).
Report `/home/ubuntu/aklt/reports/H1_FIT/report.md`, first line `STATUS: COMPLETE | PARTIAL (reason)`; write the
anatomy and the candidate table as soon as you have them (within the first hour), then keep the report current;
end with an ORCH-SUMMARY (≤ 25 lines). This task was issued by the orchestrator (Fable); do the design, numerics
and pilots yourself.

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
