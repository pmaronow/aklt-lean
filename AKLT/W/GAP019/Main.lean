module
public import AKLT.Blueprint.Gap.NodesFinite

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Gap

namespace AKLT.W.GAP019

local instance (α : Type) : DecidableEq α := Classical.decEq α

 theorem main : AKLT.Blueprint.Gap.MultiplicityEstimateStatement := by
  intro ι J _ _ _ S _ p hp B t hmult f
  classical
  have hnonneg (x : ι) : 0 ≤ blockDirichlet p {x} f := by
    unfold blockDirichlet
    apply Finset.sum_nonneg
    intro σ hσ
    exact mul_nonneg (le_of_lt (hp.1 σ)) (Complex.normSq_nonneg _)
  calc
    (∑ x, ((Finset.univ.filter fun a => x ∈ B a).card : ℝ) * blockDirichlet p {x} f)
        ≤ ∑ x, (t : ℝ) * blockDirichlet p {x} f := by
          apply Finset.sum_le_sum
          intro x hx
          apply mul_le_mul_of_nonneg_right _ (hnonneg x)
          exact_mod_cast hmult x
    _ = (t : ℝ) * dirichlet p f := by
          rw [dirichlet, ← Finset.mul_sum]

end AKLT.W.GAP019
