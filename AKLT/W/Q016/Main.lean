module
public import AKLT.Blueprint.Q.NodesStar

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators

namespace AKLT.W.Q016

open AKLT.Blueprint.Q
open AKLT.Defs

/-- Every summand of the star Hamiltonian is an orthogonal projection, hence
symmetric and positive semidefinite. -/
theorem main : AKLT.Blueprint.Q.StarPositiveStatement := by
  classical
  constructor
  · intro ψ χ
    change inner ℂ (∑ j : Fin 4,
      (Module.End.eigenspace (starCasimir j) (20 : ℂ)).starProjection ψ) χ =
      inner ℂ ψ (∑ j : Fin 4,
        (Module.End.eigenspace (starCasimir j) (20 : ℂ)).starProjection χ)
    rw [inner_sum, sum_inner]
    apply Finset.sum_congr rfl
    intro j hj
    exact (Module.End.eigenspace (starCasimir j) (20 : ℂ)).starProjection_isSymmetric ψ χ
  · intro ψ
    change 0 ≤ (inner ℂ ψ (∑ j : Fin 4,
      (Module.End.eigenspace (starCasimir j) (20 : ℂ)).starProjection ψ)).re
    rw [inner_sum, Complex.re_sum]
    apply Finset.sum_nonneg
    intro j hj
    let E := Module.End.eigenspace (starCasimir j) (20 : ℂ)
    change 0 ≤ (inner ℂ ψ (E.starProjection ψ)).re
    rw [← E.inner_starProjection_left_eq_right ψ ψ]
    exact E.re_inner_starProjection_nonneg ψ

#print axioms main

end AKLT.W.Q016
