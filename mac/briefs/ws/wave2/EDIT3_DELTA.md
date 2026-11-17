# EDIT3_DELTA — check a set of edits to a mathematics paper

Directory `/home/ubuntu/aklt/manuscript-v2` (git repository; LaTeX paper `main.tex` with section files). The
working tree contains uncommitted edits relative to the last commit (`git diff`; ignore `main.pdf`). The edits were
meant to (i) repair a small number of minor mathematical or expository defects, each described in the reports
`/home/ubuntu/aklt/reports/REF2_6/report.md` and `/home/ubuntu/aklt/reports/REF2_7/report.md` (items marked Minor),
and (ii) mark with the macro `\certpending{}` the statements whose finite computer-assisted certificates are not
yet verified. The editor's own account is `/home/ubuntu/aklt/reports/EDIT_3/report.md`.

Your task (read-only on the paper; write only your report):
1. For every hunk of the diff: is the new text mathematically correct, does it actually repair the defect it was
   meant to repair, is it consistent with every other place in the paper that uses the changed statement, constant,
   or notation (search the whole paper for uses), and does it introduce anything new that is wrong or unproved?
2. Is any Minor item of the two reports left unrepaired or only partly repaired?
3. Is `\certpending{}` placed at exactly the statements that depend on unverified finite certificates (no more,
   no fewer), and does the paper's text describe the status truthfully?
4. Does the paper compile (`latexmk -pdf -interaction=nonstopmode main.tex` in a COPY of the directory under
   your report directory; do not write in the original) without undefined references or citations?
Report `/home/ubuntu/aklt/reports/EDIT3_DELTA/report.md`: first line `VERDICT: CLEAN | FIXES NEEDED`, then one entry
per finding with file, line, what is wrong, and the exact corrected text you propose; then a list of hunks checked
with a one-line verdict each. Be concrete; do not rewrite the paper's style.
