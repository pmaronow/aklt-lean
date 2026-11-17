module
public import AKLT.Cert.H1.Production.TopLeaves
public import AKLT.W.H1C006.Central

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators ComplexOrder
open AKLT.Defs AKLT.Blueprint.H1

namespace AKLT.W.H1C006

theorem posDef_of_positive_real_scale {ι : Type*} (M : Matrix ι ι ℂ)
    (k : ℝ) (hk : 0 < k) (h : (k • M).PosDef) : M.PosDef := by
  have hs := h.smul (inv_pos.mpr hk)
  simpa only [smul_smul, inv_mul_cancel₀ hk.ne', one_smul] using hs

/-- The entire positive-scale step follows from the exact entry identity.
Neither optional Sylvester nor Bareiss facts are used. -/
theorem positiveScale_of_thresholdScale
    (hScale : AKLT.Cert.H1.Production.TopLeaves.thresholdScale) :
    AKLT.Cert.H1.Production.TopLeaves.positiveScale := by
  intro π hπ r I hI D₀ hD₀ p q hp hq hpq ε
  let M := complexSectorMatrix π r ε (invertPolynomial I (reducedDifference π r ((p : ℚ) / q)))
  let k : ℝ := 15 * (D₀ : ℝ) * q
  have hk : 0 < k := mul_pos (mul_pos (by norm_num) (by exact_mod_cast hD₀.1))
    (by exact_mod_cast hq)
  have heq : (thresholdSectorMatrix π r ε I D₀ p q).map (Int.castRingHom ℂ) = k • M := by
    ext a b
    change (thresholdSectorMatrix π r ε I D₀ p q a b : ℂ) = (k : ℂ) * M a b
    have hc : (k : ℂ) = 15 * (D₀ : ℂ) * q := by
      dsimp only [k]
      push_cast
      rfl
    rw [hc]
    exact hScale π hπ r I hI D₀ hD₀ p q hp hq hpq ε a b
  rw [heq]
  exact ⟨fun h => h.smul hk, posDef_of_positive_real_scale M k hk⟩

theorem central_matrix_positive_of_indexed
    (hScale : AKLT.Cert.H1.Production.TopLeaves.thresholdScale)
    (π : PatternData) (hπ : π.Covered) (r : Representation)
    (I : Finset (Fin 20)) (hI : GroupInversion π r I)
    (D₀ : ℕ) (hD₀ : ClearsDenominator π r D₀)
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hpq : (p : ℚ) / q < 1)
    (hPositive : ∀ ε : ExchangeSigns π, ∃ t : ℕ, ∃ index : Fin t ≃ CentralBasis π r ε,
      ((indexedSectorMatrix π r ε I D₀ p q index).map (Int.castRingHom ℂ)).PosDef) :
    ∀ ε : ExchangeSigns π,
      (complexSectorMatrix π r ε (invertPolynomial I (reducedDifference π r ((p : ℚ) / q)))).PosDef := by
  intro ε
  obtain ⟨t, index, h⟩ := hPositive ε
  have hi := h.submatrix index.symm.injective
  have heq : (((indexedSectorMatrix π r ε I D₀ p q index).map (Int.castRingHom ℂ)).submatrix
      index.symm index.symm) = (thresholdSectorMatrix π r ε I D₀ p q).map (Int.castRingHom ℂ) := by
    ext a b
    change (thresholdSectorMatrix π r ε I D₀ p q (index (index.symm a)) (index (index.symm b)) : ℂ) =
      (thresholdSectorMatrix π r ε I D₀ p q a b : ℂ)
    rw [index.apply_symm_apply, index.apply_symm_apply]
  rw [heq] at hi
  exact (positiveScale_of_thresholdScale hScale π hπ r I hI D₀ hD₀ p q hp hq hpq ε).mpr hi

end AKLT.W.H1C006
