# REF-MOS — referee a self-contained proof that replaces two cited results

You are an independent referee. The proof will be formalized in Lean 4, so check every step adversarially.

**Inputs (read-only).** `/home/ubuntu/aklt/review/REF-MOS/proof.tex` — a LaTeX appendix proving that a "window
estimate" for a finite-alphabet, translation-invariant, range-one lattice model on Z² implies a uniform spectral gap
of the single-site heat-bath dynamics on large rectangular boxes, uniformly in the boundary condition, with
explicit constants. It is meant to replace, in the manuscript `/home/ubuntu/aklt/manuscript/bundle/manuscript/`
(see `sec4-mixing-to-gap.tex`, Theorems 4.3 and 4.4 and their use in Corollary 4.9 / Theorem 4.10), the cited
results [MOS94, Thm 2.1] and [MO94, Thm 4.1]. Read the manuscript's Section 4 (and what it needs from Sections 3
and 5) for context. Read nothing else on this machine. You may search the web for the cited literature and
standard results the proof uses.

**Check:** every statement is well-posed and every step follows; constants (α, d, n, M, the gap bound m) are
correct; all hypotheses (shapes, boundary conditions, radii, integer parts, thresholds, the range-one and
finite-energy assumptions) are stated and used correctly; the output is exactly what the manuscript's Theorem 4.10
needs from Theorems 4.3–4.4 (box gaps for the cell models at every placement and every boundary condition, in the
form consumed by Theorem 3.x (the finite-size criterion)); nothing is circular with Section 5. You may run small
exact computations (Python with fractions) to test inequalities or small cases. At most 4 cores.

**Deliverable.** `/home/ubuntu/aklt/reports/REF-MOS/report.md`, first line exactly one of `VERDICT: SOUND`,
`VERDICT: SOUND WITH FIXES`, `VERDICT: GAP`, `VERDICT: ERROR`; then numbered findings (severity Critical / Major /
Minor, location, exact claim, why it fails, repair); a statement table (every numbered statement: content,
verdict, dependencies); formalization notes (implicit standard facts that would be Lean nodes); and an assessment
of whether the proof's conclusion plugs into the manuscript's Section 4 without change. Do not launch sub-agents.
