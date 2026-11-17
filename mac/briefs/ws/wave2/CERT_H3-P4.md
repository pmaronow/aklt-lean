Orchestrator message — phase 4: fitting the external verifier's budget. Your production is complete and
accepted. New constraint, not known when the certificate was designed:

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

Your certificate as built costs about 20 CPU-hours of Lean kernel time (5,035 modules, 31.6 GB of oleans, single
modules up to 15 GiB, 248 MB of endpoint literals in a single prefix export); under the limits above it would be
kernel-checked three times (build, Lean replay, NanoDa at 2–5x Lean on your modules per measurements in
`/home/ubuntu/aklt/reports/REL_FEAS/report.md`) on 16 CPUs with 32 GiB, together with the rest of the project and
another, larger certificate. A workable share for H3′ is roughly: at most 1.5 CPU-hours of Lean kernel time in
total, at most 6 GiB per process, at most a few hundred MB of exported literals, files of at most 10,000 lines.

Task (design and measured micro-pilots only; do NOT rebuild production, do not edit files on `main`; work in your
worktree under a new directory `Fit/` and your report directory; at most 8 Lean processes and 60 GB RAM — a long
production job of another lane is running):
1. Break down your 20 CPU-hours and your memory/literal volume by stage and by cause (which checks, which data,
   what is recomputed per module, what is import/elaboration overhead rather than kernel reduction).
2. List every way to cut it, from engineering (sharing, batching, cheaper encodings, fewer and larger or more and
   smaller modules, avoiding re-elaboration of literals) to mathematical (a different certificate for the same
   statement `StationaryCheckStatementV2`/`Automaton10StatementV2`: smaller memory, shorter prefixes, a coarser
   potential, symmetry reduction, a different inequality that needs fewer rows) — for each, the expected factor,
   what would have to be re-proved or re-searched, and the risk. Use the search programs and data in your lane to
   test numerically (outside Lean) whether a cheaper certificate exists where that is quick to try.
3. For the best one or two, a measured micro-pilot in Lean (kernel time, memory, export size under con-ron and
   NanoDa via `/home/ubuntu/aklt/bin/conron-check.sh`-style runs) that supports the claimed factor.
4. A verdict: can H3′ reach the share above (yes with plan / only to factor X / no), and the work needed.
Update `report.md` with a section "phase 4 — fit" (first line of the file `STATUS: …`), ORCH-SUMMARY ≤ 20 lines.
