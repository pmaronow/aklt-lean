# ASSEMBLE — assemble the revised AKLT gap paper from its section files

**Inputs.** The plan `/home/ubuntu/aklt/reports/REV-PLAN/PLAN.md` ("Paper order and file ownership" table and the
statement inventory); the section files written from it: `/home/ubuntu/aklt/reports/REV_A1/{sec1-result,sec3-quantum-frames}.tex`,
`REV_A2/{sec4-periodic-gap,app-finite}.tex`, `REV_B/{sec5-window,app-topology}.tex`,
`REV_C1a/{sec2-moments,sec6-walks}.tex`, `REV_C1b/sec7-recursion.tex`,
`REV_C2/{sec8-inputs,app-input-contracts}.tex`, `REV_C3/app-local-operator.tex` (each lane's `report.md` lists its
deviations from the plan and, where present, its responses to a first review); the previous version of the paper
`/home/ubuntu/aklt/manuscript-corrected/` (main.tex: macros, title, bibliography).

**Task.** In a new git-initialized directory `/home/ubuntu/aklt/manuscript-v2/` build the complete revised paper:
`main.tex` (title unchanged; a new abstract and a short introduction-level first paragraph consistent with §1 —
state the theorem for all L, N ≥ L₀ of any parity and uniqueness for all L, N ≥ 3, the computer-assisted inputs as
now designed, and that all computations are checked in exact arithmetic; plain, serious prose, American spelling,
serial comma), the twelve section files in the plan's order (copied; edit them only as specified below), and the
bibliography (keep only cited entries; add any entry a section cites). Then make the paper coherent:
1. every `\ref`/`\eqref`/`\cite` resolves; no duplicate labels; consistent macros and notation across files;
2. every use of a statement from another file matches that statement's actual hypotheses and conclusion as
   written in the owning file (check each cross-file citation; fix pure label/notation mismatches in place; for a
   MATHEMATICAL mismatch do not paper over it — fix it only if the fix is a one-line hypothesis/citation repair that
   is clearly intended, and in every case list it);
3. each lane's listed deviations from the plan are propagated to the files that use the changed statements;
4. remove from the text any editorial history (mentions of plans, lanes, reviews, earlier versions, agents), and
   strip LaTeX comments.
Build with `latexmk -pdf` (0 undefined references). Do not change mathematical content beyond item 2.

**Deliverables.** The directory (uncommitted is fine; `main.pdf` built); `/home/ubuntu/aklt/reports/ASSEMBLE/report.md`
with first line `STATUS: COMPLETE` or `STATUS: PARTIAL (reason)`, the list of cross-file checks (use → owner →
match?), every mismatch and what you did, every edit to a section file (file:line, before/after), and an
ORCH-SUMMARY (≤ 25 lines). Write only in those two directories. Do not launch sub-agents.
