# Fidelity review FID-CH-G3 (blind)

**Your group of declarations:** SpinorPolynomial, singlet, vbsPolynomial, monomialDegree, B (does B equal the valence-bond-solid state of (e:B) in the coordinates of Hilbert, consistently with the spin model used by P, up to a nonzero scalar at most?). Read the whole file for context; judge only your group.

Your working directory is `/home/ubuntu/aklt/reports/FID-CH-G3/`.

**Inputs (read-only).** The Lean file `/home/ubuntu/aklt/review/FID-CH/Main.lean` (a copy of a Challenge file that
states the main theorem of a manuscript in Lean 4 + Mathlib), and the manuscript
`/home/ubuntu/aklt/manuscript/bundle/manuscript/` (`main.pdf` and .tex sources; read §1 and §2 in full). Read
nothing else on this machine except Mathlib sources (under
`/home/ubuntu/aklt/repo/.lake/packages/mathlib/Mathlib/`) to check what Mathlib definitions mean.

**Your job.** Decide, for every declaration in your group, whether the Lean text says exactly what the manuscript
says: nothing weaker, nothing stronger, no degenerate or vacuous reading. Check the meaning of every Mathlib
definition used (look it up in the Mathlib source; e.g. what `Module.End.eigenspace`, `starProjection`,
`Matrix.toEuclideanLin`, `MvPolynomial.coeff`, `Finsupp.equivFunOnFinite`, `HasEigenvalue`, `ZMod`, `EuclideanSpace`
mean exactly), coercions (ℕ→ℝ→ℂ, subtraction on ℕ), index conventions, normalizations and orientation conventions,
and whether quantifiers and domains match (parities, size thresholds, L, N ≥ 3). You may run small computations
(Python 3, or Lean in a scratch copy under your own directory, linking Mathlib packages from
`/home/ubuntu/aklt/repo/.lake/packages` with a symlink; at most 2 Lean processes) to test claims on small cases,
e.g. matrix identities on one or two sites.

**Deliverable.** `report.md` in your working directory. First line exactly `STATUS: PASS` or `STATUS: FAIL`;
second line exactly `BLOCKING: n` (the number of blocking problems). Then one row per declaration of your group:
`DECL: <name> PASS` or `DECL: <name> FAIL`, each followed by your reasoning (the manuscript text it must match,
with file:line, and the Mathlib meaning you checked). Then non-blocking remarks. A problem is blocking if the
Lean statement would differ in meaning from the manuscript or could be proved or refuted for a reason the
manuscript does not intend. Do not launch sub-agents. Do not modify the input files.
