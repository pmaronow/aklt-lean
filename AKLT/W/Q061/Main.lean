module
public import AKLT.W.Q061.Tensorization

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.Q061

theorem product_dirichlet {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ x, Fintype (S x)]
    (p : (x : ι) → Weight (S x)) (hp : ∀ x, PositiveProbability (p x))
    (f : ((x : ι) → S x) → ℂ) :
    dirichlet (productMass p) f = ∑ x, energy p (f - siteAverage p x f) := by
  classical
  simp only [dirichlet, blockDirichlet, energy,
    conditionalExpectation_singleton p hp, Pi.sub_apply]

/-- The product Poincare inequality with rate one at each site. -/
theorem main : AKLT.Blueprint.Q.ProductPoincareStatement := by
  intro ι _ _ S _ p hp f
  rw [one_mul]
  change variance (productMass p) f ≤ dirichlet (productMass p) f
  rw [product_dirichlet p hp]
  exact product_tensorization p hp f

end AKLT.W.Q061

#print axioms AKLT.W.Q061.main
