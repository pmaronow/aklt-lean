# Blind referee — one part of a mathematics paper, with the whole paper available

You are an independent referee. The paper will be formalized in Lean 4, so check adversarially: every gap you miss
becomes a stuck or false Lean node.

**Inputs (read-only)** in `/home/ubuntu/aklt/review/REF2/paper/`: the complete LaTeX source (`main.tex` and section
files) and `main.pdf`. Read nothing else on this machine. You may search the web for standard results.

**Your part:** __PART__. Read the whole paper for context; check your part line by line. For results your part
uses from other parts, check that they are used within their stated hypotheses (you need not re-prove them).
Check: well-posedness of every statement; every proof step; all hypotheses and edge cases (sizes, parities,
boundary, empty sets, zero denominators, signs); constants; consistency of notation with the rest of the paper.
You may run exact computations (Python with fractions/sympy, C; at most 4 cores).

**Deliverable.** `/home/ubuntu/aklt/reports/__KEY__/report.md`: first line one of `VERDICT: SOUND`,
`VERDICT: SOUND WITH FIXES`, `VERDICT: GAP`, `VERDICT: ERROR`; numbered findings (Critical / Major / Minor;
file:line and label; exact claim; why it fails; repair as exact LaTeX where possible); a statement table for your
part (label, content, verdict, dependencies); formalization notes; and a final section `ORCH-SUMMARY` (≤ 20 lines).
Do not launch sub-agents. Do not modify inputs.
