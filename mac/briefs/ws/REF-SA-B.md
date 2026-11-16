# REF-SA-B — referee the analytic part of a strengthening of the main theorem

**Your part:** Sections 3, 4 and 5 of proof.tex (unchanged finite-size criterion and the replacement remark r:Kpins; inhomogeneous cells and uniform finite energy e:energy; Lemmas l:compare, l:boxcell with the local gauge e:localgauge; the uniform window hypothesis d:W and the stopped coupling l:stopped; the box-gap corollary c:gapcell with its constants e:nchoice, e:cellconstants; the replacement proof of t:mainW and e:ellchoice; the quadrature lemma l:exact for different frames, the cut ratio and t:cutMOS with e:windowconstants), the retained-inputs section, and the replacement constants section. Read the rest for context. Your working directory is `/home/ubuntu/aklt/reports/REF-SA-B/`.

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
