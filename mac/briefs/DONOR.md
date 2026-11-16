# Donor search and Lean literature review — AKLT spectral-gap formalization

**Goal.** We will formalize in Lean 4 + Mathlib (no `sorry`, no `native_decide`, axioms only propext,
Classical.choice, Quot.sound; Palomar Comparator standard) the manuscript in
`/Users/paronow/aklt-lean/bundle/manuscript/` (read `main.pdf` or the .tex files to understand what is needed;
read nothing else from the bundle except `bundle/README.md`). Find existing Lean code (and, secondarily, Coq/Isabelle
developments and techniques) we can reuse or imitate, so that writers import instead of re-proving.

**Components to cover** (map each to concrete repositories/files/declarations):
1. SU(2) representations: spin-j as Sym^{2j}(C^2), tensor products, total-spin projections, Clebsch–Gordan,
   spin coherent states, valence-bond / AKLT states, frustration-free Hamiltonians, spectral gaps of finite
   Hermitian matrices (Courant–Fischer, min-max), Knabe / Gosset–Mozgunov finite-size criteria, detectability lemma.
2. Spherical designs and polynomial integration on S^2: uniform measure on the sphere, moments of monomials,
   icosahedron/dodecahedron vertices (golden ratio arithmetic), tight frames.
3. Finite Markov chains and Gibbs measures: reversible generators, Dirichlet forms, Poincaré inequality / spectral
   gap, heat-bath (Glauber) dynamics, conditional expectations on finite product spaces, block dynamics, variance
   decompositions, total variation distance and optimal couplings on finite sets, strong/weak spatial mixing,
   Martinelli–Olivieri / Martinelli–Olivieri–Schonmann type results, Holley-type recursions, finite speed of
   propagation.
4. FKG / Harris / four-functions theorem (Mathlib has some), correlation inequalities.
5. Planar lattice topology on Z^2: *-connectivity, boundary connectivity (Timár 2013), cut sets, Kesten-type
   duality, discrete Jordan-curve style lemmas.
6. Walks and trails on graphs (Mathlib SimpleGraph.Walk, IsTrail), counting weighted walks, transfer matrices.
7. Nonnegative matrices: Perron–Frobenius, Collatz–Wielandt bounds, spectral radius via sub-invariant vectors.
8. Kernel-checked computation WITHOUT native_decide: exact rational / dyadic interval arithmetic, `decide`,
   `decide +kernel`, `Nat`/`Int` GMP acceleration in the kernel, verified positive-definiteness checks
   (Bareiss, LDL^T, Cholesky certificates), large kernel-checked computations in Lean 4 (what sizes have been done,
   how long they took), proof-by-reflection libraries, verified interval arithmetic libraries in Lean 4.
9. Any formalization of quantum spin systems, AKLT, valence-bond solids, Heisenberg models, or spin-glass/Ising
   Glauber dynamics.

**Sources you must search (record coverage for each):** Palomar (the registry and the authors' `*-palomar`
packages); Statlib/StatLean; CausalLean; GitHub code search; https://github.com/pmaronow/llm-audit-lean and every
repository it cites; all repositories of the GitHub user `pmaronow` (list them with `gh repo list pmaronow
--limit 200`; several contain Glauber dynamics, spectral gaps, Gibbs measures, Markov chains); Mathlib (current
master and the v4.34–v4.36 era); PhysLean (formerly HepLean); Lean-QuantumInfo; other Lean 4 physics or
probability libraries you find; the Lean Zulip archive for kernel-computation and interval-arithmetic techniques.

**Rules.** Read-only on GitHub: never push, comment, open issues or star. Clone only into
`/Users/paronow/aklt-lean/reports/DONOR/clones/` (shallow or blobless clones; total ≤ 4 GB; delete clones you no
longer need before finishing). Do not run Lean builds (no Lean is installed here). Do not launch sub-agents.

**Deliverable:** `/Users/paronow/aklt-lean/reports/DONOR/donors.md` with
1. a status line `STATUS: COMPLETE` or `STATUS: PARTIAL (reason)`;
2. a per-source coverage record (source, what was searched, what was found or "nothing relevant");
3. a component table: component → candidate repository, file, declaration names, Lean/Mathlib version, licence,
   fit (direct import / adapt / pattern only), and the effort it saves;
4. for item 8, a concrete summary of what is known about the speed of kernel evaluation (with sources) and the best
   available design for checking large exact computations without native_decide;
5. a recommended vendoring list (what to copy at which commit, with licence and attribution notes).
Every claim about a repository must cite the path (and commit or date) you looked at.
