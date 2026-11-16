# DELTA-1 — referee the correction edit of the manuscript

**Inputs (read-only).** The manuscript working copy `/home/ubuntu/aklt/manuscript-corrected/` (git): the frozen
version is commit 32487a2; the corrections are commits ade1a62, 13b8ecf, 720cfb7, 9222abe (one per adjudication
report: ADJ-R4, ADJ-R5, ADJ-R6, ADJ-MINOR; each cumulative). The adjudication reports that define the corrections:
`/home/ubuntu/aklt/reports/ADJ-R4/report.md`, `ADJ-R5/report.md`, `ADJ-R6/report.md`, `ADJ-MINOR/report.md`.
The editor's account: `/home/ubuntu/aklt/reports/EDIT-1/report.md`. Use `git diff 32487a2 9222abe` and per-commit
diffs.

**Check:** (1) every CONFIRMED / CONFIRMED-MODIFIED finding is implemented, using the adjudicator's correction, and
correctly (re-derive each corrected statement and proof step); (2) no edit changes anything that no finding required,
and no edit introduces an error, an inconsistency with an unchanged passage, a broken reference or label, or a
weaker or different main theorem; (3) statements about archived programs and outputs are accurate (the full project
tree is at `/home/ubuntu/aklt/source-full/`); (4) the PDF builds (`latexmk -pdf` in a copy under your own dir).
Write only in your working directory `/home/ubuntu/aklt/reports/DELTA-1/`. Do not modify the repository.

**Deliverable.** `report.md`, first line `VERDICT: ACCEPT` or `VERDICT: ACCEPT WITH FIXES` or `VERDICT: REJECT`;
then a table finding-id → implemented correctly? (yes/no/partly) with evidence; then every problem found (severity,
file:line, the fix as exact LaTeX). Do not launch sub-agents.
