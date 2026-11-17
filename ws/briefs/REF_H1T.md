# REF_H1T — referee a section of a mathematics paper

You are refereeing a section intended for the paper in `/home/ubuntu/aklt/manuscript-v2` ("The spectral gap of
the spin-2 AKLT model on the square lattice"; read `sec6-walks.tex` and `sec7-recursion.tex` for the definitions
and for how the input called (H1) is used, and `sec2-moments.tex` for the moment lemmas). The section is
`/home/ubuntu/aklt/reports/H1TREE_PROOF/h1tree.tex` (PDF: `wrapper.pdf` in the same directory); it states a finite
list of inequalities on small models, the finite computer checks that certify them, and a theorem deriving from
them the local inequality that Sections 6–7 need. The directory also has the exact data and replay programs
(`checks/`, `data/`).

Referee it as you would for a journal, for correctness and completeness only:
1. Check every definition, lemma and proof step line by line against the paper's own definitions. For each
   numbered statement give a verdict (correct / gap / error) with the reason. Pay particular attention to: what
   exactly is integrated and conditioned on at each step; whether each mean bound is applied with its hypotheses
   satisfied (how many fields, which radii, which law); the treatment of pinned sites; whether the weights of each
   convex decomposition are identical for the two partition functions being compared; whether the case analysis
   is exhaustive for every local configuration the paper's definitions allow; and whether the conclusion is
   exactly what Sections 6–7 use (find every place those sections invoke (H1) and check the section's theorem
   suffices there, including the exceptional departures).
2. Check the computer-assisted parts: is each finite check stated precisely enough to be reproduced, does the
   stated check really imply the lemma it is attached to (e.g. nonnegative Bernstein coefficients ⇒ nonnegativity
   on the stated domain; Gram/residual witness ⇒ the matrix inequality; the scalar tests ⇒ the scalar
   inequality), and does the replay program do what the text says (read it; run it; you may write small
   independent tests of your own, including random numerical tests of individual lemmas).
Report `/home/ubuntu/aklt/reports/REF_H1T/report.md`: first line
`VERDICT: SOUND | SOUND WITH FIXES | GAP | ERROR`, then findings ordered by severity (Fatal / Major / Minor), each
with location, what is wrong, and what would fix it; then the per-statement table. Write only under
`/home/ubuntu/aklt/reports/REF_H1T`. Up to 4 CPU-heavy processes.
