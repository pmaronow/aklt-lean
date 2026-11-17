# EDIT_3 — apply referee corrections to the assembled paper

**Working copy:** `/home/ubuntu/aklt/manuscript-v2/` (LaTeX; build with `latexmk -pdf main.tex`). Seven referees
reviewed it part by part: `/home/ubuntu/aklt/reports/REF2_1 … REF2_7/report.md` (five SOUND; REF2_5 two Minor; REF2_6
one Critical and two Minor). Apply every finding that is a genuine defect of the text, minimally and exactly
(re-derive each correction; do not change anything else): REF2_5's two Minor items (closure lemma neighbour
pairs; domain of the prescribed short-trail orderings) and REF2_6's two Minor items (exact within-type order and
long-trail qualification in the phase expansion; terminal-data hypothesis in the stopped quotient intertwining),
and any Minor item in the other five reports. For REF2_6's Critical finding (the computational input theorems are
asserted unconditionally while their certificates are not yet verified): do NOT weaken the theorems; make the
text accurate — state precisely which finite checks constitute the certificates, that they are verified by the
Lean kernel in the accompanying formalization, and mark each such check with a clearly visible placeholder macro
`\certpending{...}` (define it in main.tex to print "[certificate check pending]") so that it can be removed when
the Lean certificates are complete. Keep American spelling, serial comma, plain prose; no editorial history.
**Deliverables:** edited files (git-commit is not available to you; leave them uncommitted);
`/home/ubuntu/aklt/reports/EDIT_3/report.md` with first line `STATUS: COMPLETE` or `STATUS: PARTIAL (reason)`, a
table finding → file:line → before/after, the list of `\certpending` sites, and an ORCH-SUMMARY. Write only in
those two directories. No sub-agents.
