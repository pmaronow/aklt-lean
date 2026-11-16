# MOSPROOF — complete, formalization-ready proofs of the two cited mixing results

**Context.** We are formalizing in Lean 4 (no hypotheses allowed) the manuscript in
`/home/ubuntu/aklt/manuscript/bundle/manuscript/` ("The spectral gap of the spin-2 AKLT model on the square
lattice"; `main.pdf` and the .tex files). Its Section 4 (`sec4-mixing-to-gap.tex`) uses two cited results, stated
there as Theorem 4.3 = [MOS94, Theorem 2.1] (Martinelli–Olivieri–Schonmann, CMP 165 (1994) 33–47) and Theorem 4.4
= [MO94, Theorem 4.1] (Martinelli–Olivieri, CMP 161 (1994) 447–486), applied to "cell models" with a finite
single-cell space of 57,600 elements, a translation-invariant nearest-neighbour potential of range 1 with finite
energy (Remark 4.5 explains why the paper believes MO94's ±1 proof applies to a general finite S). The author has
decided that these results must be PROVED in Lean, not assumed. Background notes on the two papers (by an earlier
reader) are in `/home/ubuntu/aklt/manuscript/MO-MOS1994-notes.md`. Find the original papers on the web (Project
Euclid hosts Communications in Mathematical Physics of these years) and any later simpler proofs (e.g. Martinelli's
Saint-Flour lecture notes "Lectures on Glauber dynamics for discrete spin models" (1999), Cesi's quasi-factorization
papers, Bertini–Cancrini–Cesi, block-dynamics/recursive arguments, Dyer–Sinclair–Vigoda–Weitz "Mixing in time and
space", and others you find).

**Task.** Write complete, self-contained proofs of exactly what Section 4 of the manuscript needs, in the generality
it needs (finite single-spin space S, translation-invariant finite-range potential with finite energy on Z²,
heat-bath dynamics), choosing the SIMPLEST rigorous route — you need not follow MO94/MOS94 if another argument
proves the same conclusion. Concretely:
1. Determine precisely what Section 4 uses from the two results (read §4 and how Theorem 4.10 / Corollary 4.9 use
   Theorems 4.3–4.4 and Proposition 4.7); if the chain "window estimate (Prop. 4.7 input) ⇒ uniform heat-bath gap on
   the relevant boxes" can be proved more directly than through SM(C_M′) for all M′ and MO94's compatible sets, say
   so and prove the direct version, stating exactly the replacement statements.
2. Prove everything from the definitions with finite-state tools only: finite probability spaces, conditional
   expectations, variances, Dirichlet forms and the variational definition of the spectral gap, total variation and
   optimal couplings on finite sets, block dynamics and their comparison with single-site dynamics, recursive
   (Holley/Martinelli-type) bounds, finite-speed-of-propagation estimates if used. Avoid continuous-time semigroups
   and limits unless unavoidable; if a step uses one, give a finite-dimensional replacement.
3. Make every constant explicit or give an explicit existence argument, and state every lemma with all hypotheses
   (shapes of regions, boundary conditions, parities, size thresholds).

**Output.** `/home/ubuntu/aklt/reports/MOSPROOF/proof.tex` (a LaTeX appendix, compilable on its own with
`amsart`), and `/home/ubuntu/aklt/reports/MOSPROOF/report.md` with first line `STATUS: COMPLETE` or
`STATUS: PARTIAL (reason)`, then: the exact statements proved; how they plug into the manuscript's Section 4 (which
statements of the manuscript change, if any, with proposed replacement text); a dependency list of all lemmas;
the sources used for each step with precise locators; and any point where the manuscript's own use of the cited
results is wrong or insufficient. Do not launch sub-agents. Do not stop before both files exist.
