module
public import AKLT.W.H1C003.Scaling

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

namespace AKLT.W.H1C003

open AKLT.Defs
open AKLT.Cert.H1.Production.TopLeaves
open scoped BigOperators ComplexOrder

private theorem posDef_smul_iff {ι : Type*} (M : Matrix ι ι ℂ) {c : ℂ}
    (hc : 0 < c) : (c • M).PosDef ↔ M.PosDef := by
  constructor
  · intro h
    have hinv : 0 < c⁻¹ := inv_pos.mpr hc
    have h' := h.smul hinv
    simpa [smul_smul, inv_mul_cancel₀ (ne_of_gt hc)] using h'
  · intro h
    exact h.smul hc

theorem positiveScale_of_thresholdScale (hthreshold : thresholdScale) :
    AKLT.Cert.H1.Production.TopLeaves.positiveScale := by
  intro π hπ r I hI D₀ hD p q hp hq hratio ε
  have hDpos : 0 < D₀ := hD.1
  let c : ℂ := (15 * D₀ * q : ℕ)
  have hc : 0 < c := by
    dsimp [c]
    exact_mod_cast (Nat.mul_pos (Nat.mul_pos (by decide) hDpos) hq)
  have hscale := hthreshold π hπ r I hI D₀ hD p q hp hq hratio ε
  have hmat : (thresholdSectorMatrix π r ε I D₀ p q).map (Int.castRingHom ℂ) =
      c • complexSectorMatrix π r ε
        (invertPolynomial I (reducedDifference π r ((p : ℚ) / q))) := by
    ext a b
    change ((thresholdSectorMatrix π r ε I D₀ p q a b : ℤ) : ℂ) =
      c * complexSectorMatrix π r ε
        (invertPolynomial I (reducedDifference π r ((p : ℚ) / q))) a b
    rw [hscale a b]
    simp only [c]
    norm_num [Nat.cast_mul, Nat.cast_ofNat, mul_assoc]
  rw [hmat]
  exact (posDef_smul_iff _ hc).symm

theorem main : AKLT.Cert.H1.Production.TopLeaves.positiveScale :=
  positiveScale_of_thresholdScale thresholdScale_proof

#print axioms positiveScale_of_thresholdScale
#print axioms main

end AKLT.W.H1C003
