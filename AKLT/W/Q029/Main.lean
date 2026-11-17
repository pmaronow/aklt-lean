module
public import AKLT.W.Q029.Diagonal
public import AKLT.W.Q029.Eigenvectors

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open AKLT.Blueprint.Q

namespace AKLT.W.Q029

/-- The orthogonal complement of diagonal evaluation's kernel has Casimir twenty. -/
theorem main : AKLT.Blueprint.Q.PairTopInclusionStatement := by
  change (LinearMap.ker pairDiagonal)ᗮ ≤ Module.End.eigenspace pairCasimir 20
  apply pairTopSpan.trans
  apply Submodule.span_le.mpr
  rintro v ⟨m, rfl⟩
  exact diagonalAdjointVector_eigen m

#print axioms pairAt_left_apply
#print axioms pairAt_right_apply
#print axioms sum_filter_left
#print axioms sum_filter_right
#print axioms pairZ_on_diag
#print axioms inner_diagonalAdjointVector
#print axioms pairDiagonal_terms
#print axioms pairDiagonal_expansion
#print axioms pairTopSpan
#print axioms pairU_zero
#print axioms pairU_succ
#print axioms pairD_on_diag
#print axioms diagonalAdjointVector_nine
#print axioms pairU_on_diag_nat
#print axioms pairD_on_diag_nat
#print axioms pairZ_on_diag_nat
#print axioms diagonalAdjointVector_eigen
#print axioms main

end AKLT.W.Q029
