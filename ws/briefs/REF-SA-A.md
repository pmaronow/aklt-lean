# REF-SA-A — referee the algebraic part of a strengthening of the main theorem

**Your part:** Sections 1 and 2 of proof.tex (the replacement Theorem 1.1 and its proof structure; Proposition p:graphkernel and equation e:graphkernel — exact ground spaces on simple graphs of maximum degree four; Lemma l:threeframes — the three rotated icosahedral designs and the separation constant b; Lemma l:colour — proper three-colourings of all tori L, N ≥ 3; the frame model e:mucirc; the replacement Theorem t:QD with orientation signs; the replacement for the rotated convention e:muDW), plus the small-size statements in Section c:extras / the additional-consequences section. Read the rest for context. Your working directory is `/home/ubuntu/aklt/reports/REF-SA-A/`.

**Inputs (read-only).** `/home/ubuntu/aklt/review/REF-SA/proof.tex` (and `proof.pdf`): replacement and added text
that extends the main theorem of the manuscript from even torus sizes to all sizes and proves uniqueness of the
ground state for all sizes ≥ 3. The manuscript it modifies is the corrected working copy
`/home/ubuntu/aklt/manuscript-corrected/` (commit 9222abe; build a PDF in a copy under your own directory if you
want one). It also relies on `/home/ubuntu/aklt/review/REF-SA/mosproof.tex`, a refereed appendix proving that a
window estimate implies uniform box gaps. Read nothing else on this machine; you may search the web for standard
results.

**Check adversarially**, step by step, every statement in your part: well-posedness, every proof step, all
hypotheses (sizes L, N = 3 and L = ℓ+1, wrap-around bonds, repeated boundary images, signs and orientations,
inhomogeneity, uniformity of constants over colourings and translates), exact constants, and that the replaced
manuscript statements are still implied where the rest of the manuscript uses them. You may run exact computations
(Python with fractions or sympy; at most 4 cores).

**Deliverable.** `report.md` in your working directory: first line one of `VERDICT: SOUND`,
`VERDICT: SOUND WITH FIXES`, `VERDICT: GAP`, `VERDICT: ERROR`; numbered findings (Critical / Major / Minor,
location, exact claim, why it fails, repair); a statement table for your part; formalization notes. Do not launch
sub-agents. Do not modify inputs.
