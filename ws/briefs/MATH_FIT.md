# MATH_FIT — change the mathematics so that the finite inputs become cheap (author-directed, top priority)

**Context.** Paper `/home/ubuntu/aklt/manuscript-v2` ("The spectral gap of the spin-2 AKLT model on the square
lattice"; `main.tex`, sections `sec1`…`sec8`, appendices). Its proof ends in three finite computer-verified inputs
(sec8 and `app-input-contracts.tex`): (H1) an operator bound for local passage patterns (7,962 patterns, Gram /
residual certificates), (H2) a memory-6 one-step test (small), and (H3′) a stationary Bellman supersolution for a
type-dependent walk kernel (memory 10, radius 70, prefix 12, contraction ρ ≤ 0.993015). The design notes that led
to these inputs: `/home/ubuntu/aklt/reports/REV-PLAN/PLAN.md` and `interfaces.tex`. The numerical programs and data
that found the certificates: `/home/ubuntu/aklt/compfeas`, `/home/ubuntu/aklt/data/h1`, the two certificate lanes'
tools in `/home/ubuntu/aklt/wt/CERT_H1/AKLT/Cert/H1/tools` and `/home/ubuntu/aklt/wt/CERT_H3/AKLT/Cert/H3` (both
worktrees READ-ONLY), reports `/home/ubuntu/aklt/reports/CERT_H1/report.md`, `/home/ubuntu/aklt/reports/CERT_H3/report.md`.
In Lean, the kernel-checked certificates now cost ≈ 115 CPU-hours (H1) and ≈ 20 CPU-hours (H3′).

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

Two other agents are redesigning the H1 and H3′ certificates WITHIN the present mathematical statements (cheaper
checkers, encodings, symmetry). **Your task is different: change the statements.** Find a mathematically valid
variant of the paper's closing argument whose finite inputs are smaller by two orders of magnitude.
1. SLACK MAP. Trace exactly how the constants of (H1), (H2), (H3′) enter the final inequalities (the recursion and
   contraction in sec6–sec8): which numerical margins are tight, which are loose, and what trade-offs exist
   (e.g. a weaker H1 constant against a stronger walk bound; larger block scale l₀; a different thickened cut;
   different revisit penalty; a coarser type partition; fewer memory steps with a better potential).
2. ALTERNATIVES. Propose concrete alternative finite inputs, for example: an (H1) bound obtained analytically or
   from a few dozen small matrices instead of 7,962 patterns (which patterns really need the sharp constant?);
   replacing the Gram certificate family by one inequality on a transfer operator; an (H3′) with memory ≤ 6–8 and
   a hand-describable potential; a renewal/Lyapunov argument whose finite part is a single small matrix
   inequality; using the positivity/contraction structure to bound all types by one worst type. Use the existing
   numerical programs to TEST each alternative numerically (does the final inequality still close? with what
   margin? how big is the finite check — count rows, matrix sizes, integer sizes). Run real experiments; an idea
   without a number is not a result.
3. For the best one or two alternatives: the precise new statements of the inputs, the modified paragraphs of the
   closing argument (what changes in sec6–sec8, as a proof sketch with every inequality explicit), the estimated
   Lean kernel cost at the levels above, and the risk. Rank by (probability it works) × (cost reduction).
Write only under `/home/ubuntu/aklt/reports/MATH_FIT` (programs, data, report). Up to 8 CPU-heavy processes and
60 GB RAM (a production job has priority on this machine). Report `report.md`, first line
`STATUS: COMPLETE | PARTIAL (reason)`; write the slack map as soon as you have it (within the first hour), keep the
report current as experiments finish; end with an ORCH-SUMMARY (≤ 25 lines). This task was issued by the
orchestrator (Fable); do the mathematics and the experiments yourself.
