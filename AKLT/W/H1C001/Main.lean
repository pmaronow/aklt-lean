module
public import AKLT.W.H1C001.Arithmetic

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

namespace AKLT.W.H1C001

open AKLT.Defs
open scoped BigOperators ComplexOrder

/-- The reconstructed current and next forms are symmetric integer matrices,
at the prescribed scales `3D₀` and `5D₀`. -/
theorem main : AKLT.Cert.H1.Production.TopLeaves.integerEntries := by
  classical
  intro π _ r I _ D₀ hD ε next
  constructor
  · apply Matrix.IsSymm.ext
    intro a b
    change Int.floor
        ((if next then 5 else 3) * (D₀ : ℚ) *
          rationalSectorEntry π r ε
            (invertPolynomial I (reducedPolynomial π r next)) b a) =
      Int.floor
        ((if next then 5 else 3) * (D₀ : ℚ) *
          rationalSectorEntry π r ε
            (invertPolynomial I (reducedPolynomial π r next)) a b)
    rw [rationalSectorEntry_symm π r ε _ b a]
  · intro a b
    change (Int.floor
        ((if next then 5 else 3) * (D₀ : ℚ) *
          rationalSectorEntry π r ε
            (invertPolynomial I (reducedPolynomial π r next)) a b) : ℚ) =
      (if next then 5 else 3) * (D₀ : ℚ) *
        rationalSectorEntry π r ε
          (invertPolynomial I (reducedPolynomial π r next)) a b
    obtain ⟨z, hz⟩ := scaled_sector_integral π r I D₀ hD ε next a b
    rw [hz]
    simp

#check (AKLT.W.H1C001.main : AKLT.Cert.H1.Production.TopLeaves.integerEntries)
#print axioms main

end AKLT.W.H1C001
