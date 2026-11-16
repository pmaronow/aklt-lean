# EDIT-1 — apply the adjudicated corrections to the manuscript

**Working copy (yours to edit):** `/home/ubuntu/aklt/manuscript-corrected/` — a git repository holding the LaTeX
sources (`main.tex` + section files) of the manuscript under formalization, at the frozen version (commit 32487a2).
Build with `latexmk -pdf main.tex` there (delete auxiliary files you create other than `main.pdf`).

**What to apply.** Every finding marked `CONFIRMED` or `CONFIRMED-MODIFIED` in the adjudication reports
`/home/ubuntu/aklt/reports/ADJ-R4/report.md`, `ADJ-R5/report.md`, `ADJ-R6/report.md` and `ADJ-MINOR/report.md`,
using the adjudicator's correction (not the original referee's, where they differ). Skip findings marked
`REJECTED`. The referee reports the adjudicators quote are in `/home/ubuntu/aklt/referee/` if you need context.

**Rules.**
- Minimal edits: change only what a confirmed finding requires, keep labels, numbering and the paper's style
  (American spelling, serial comma, no new hedging). Do not touch the main theorem or constants unless an
  adjudicator says it is unavoidable.
- Where two corrections touch the same passage, merge them consistently.
- Statements about which programs and outputs exist: make them accurate (an adjudicator lists what is archived
  and where); do not invent new verification claims.
- After finishing each adjudication report, record a checkpoint: try `git commit -am "<report>: <finding ids>"`; if
  the sandbox does not allow writing `.git`, instead save `git diff 32487a2 > /home/ubuntu/aklt/reports/EDIT-1/after-<report>.diff`
  (cumulative diff after that report) and continue; the orchestrator will commit.

**Deliverables.** The commits or checkpoint diffs; `main.pdf` building without errors or undefined references; and
`/home/ubuntu/aklt/reports/EDIT-1/report.md` with first line `STATUS: COMPLETE` or `STATUS: PARTIAL (reason)`,
then a table: finding id → files/lines changed → commit, plus any finding you could not apply and why, and a draft
`MANUSCRIPT_DELTAS.md` section (one entry per finding: kind = correction, the counterexample or reason, before/after
text) written to `/home/ubuntu/aklt/reports/EDIT-1/MANUSCRIPT_DELTAS-part1.md`. Do not launch sub-agents.
