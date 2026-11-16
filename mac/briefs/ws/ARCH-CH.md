# ARCH-CH — the Challenge statement of the main theorem (Lean 4 + Mathlib only)

**Context.** We are formalizing, to Palomar standards, the manuscript in `/home/ubuntu/aklt/manuscript/bundle/manuscript/`
("The spectral gap of the spin-2 AKLT model on the square lattice"; read `main.pdf` or the .tex files, especially
§1 (`sec1-intro-statement.tex`) and §2 (`sec2-frames-Q.tex`), where the Hamiltonian, the valence-bond-solid state B
(equation `e:B`) and the gap are defined). The Challenge file states the headline result, Theorem 1.1, in plain
Mathlib terms: a reader who knows the physics but not our project must be able to check that it says exactly what
the paper claims — nothing weaker, nothing stronger.

**Workspace.** Worktree `/home/ubuntu/aklt/wt/ARCH-CH` (Lake project `AKLT`, Lean 4.35.0-rc2, Mathlib prebuilt and
linked; never run `lake update`; never build Mathlib). Write only in this worktree and in
`/home/ubuntu/aklt/reports/ARCH-CH/`. Compile single files with `lake env lean <file>` or `lake build <Module>`.
At most 4 Lean processes. PATH needs `$HOME/.elan/bin`. The Lean Beam MCP server is available.

**Write:**
1. `AKLT/Challenge/Main.lean`: imports only Mathlib; at most ~300 lines; ordinary readable definitions with
   docstrings citing the paper's equation labels. It defines: the torus Λ_{L,N} = ZMod L × ZMod N and its
   nearest-neighbour bonds (for L, N ≥ 3 each bond once); the site space V of spin 2 (the 5-dimensional irreducible
   representation of SU(2) — choose a concrete, standard model, e.g. ℂ⁵ with the standard spin matrices, or
   Sym⁴ℂ², and document it); the Hilbert space ⊗_x V realised concretely (e.g. functions (Λ → Fin 5) → ℂ with the
   standard inner product); for each bond e the orthogonal projection P_e onto the total-spin-4 subspace of
   V_x ⊗ V_y (characterised in a way a reviewer can check, e.g. the eigenvalue 20 = 4·5 eigenspace of the total
   spin Casimir on that bond, extended by the identity); H_{L,N} = Σ_e P_e; the valence-bond-solid state B exactly
   as in the paper; and `def MainStatement : Prop` = Theorem 1.1: there exist c > 0 and L₀ such that for all even
   L, N ≥ L₀ the kernel of H_{L,N} is the span of B and every nonzero eigenvalue of H_{L,N} is ≥ c. If you prefer
   a variational form of the gap, state the eigenvalue form in `MainStatement` and prove (in a separate file) the
   equivalence with your variational form.
2. `AKLT/Challenge/Sanity.lean` (may import the Challenge): non-vacuity and sanity facts as stated Props
   (`def ... : Prop`), each with a proof if it is cheap and with a short comment otherwise: P_e is an orthogonal
   projection; H is self-adjoint and positive semidefinite; B ≠ 0; the definitions are not degenerate for
   L = N = 4 (e.g. the number of bonds is 2LN; dim V = 5; the rank of P_e is 9 · 5^{LN−2}). Prove whatever is
   cheap; do NOT attempt H B = 0 or the main theorem.
3. `/home/ubuntu/aklt/reports/ARCH-CH/report.md`: first line `STATUS: COMPLETE` or `STATUS: PARTIAL (reason)`;
   then a table mapping each Lean definition to the paper's text (file:line), every modelling choice with its
   justification (and the alternatives you rejected), the list of Lean traps you checked (degenerate L or N,
   duplicate bonds, ZMod 0, coercions, Real vs Complex inner products, `LinearMap.ker` vs eigenvalue 0, `finrank`
   assumptions, implicit `Fintype`/`DecidableEq` instances), and the output of `#print axioms` for every proved
   sanity theorem.

**Soundness rules.** No `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `extern`, `unsafe`, `opaque`
in any file you deliver (state unproved facts as `def ... : Prop`). Allowed axioms: propext, Classical.choice,
Quot.sound. Do not launch sub-agents. Do not stop before the files and the report exist.
