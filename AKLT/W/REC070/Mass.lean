module
public import AKLT.W.REC070.TrailBound

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators ENNReal
open AKLT.Defs AKLT.Blueprint.Rec
namespace AKLT.W.REC070
set_option maxHeartbeats 2000000
attribute [local instance] Classical.propDecidable

lemma coefficient_total (X : PairType) (n : ℕ) :
    (∑ Y : PairType, ∑ s ∈ Finset.range (n + 2), kernelLengthCoefficient X Y s n) =
      ∑ w : DirectionWord n, if ClosedTrail X w then
        trailBaseWeight kernelStart w * exposureSum w
          (fun i => ∑ Y : PairType, ∑ s ∈ Finset.range (n + 2), responseKappa X Y s w i)
          (kernelOrdering w) else 0 := by
  unfold kernelLengthCoefficient
  calc
    _ = ∑ w : DirectionWord n, ∑ Y : PairType, ∑ s ∈ Finset.range (n + 2),
        if ClosedTrail X w then
          trailBaseWeight kernelStart w * exposureSum w (responseKappa X Y s w) (kernelOrdering w)
        else 0 := by
      simp_rw [Finset.sum_comm (s := Finset.range (n + 2)) (t := (Finset.univ : Finset (DirectionWord n)))]
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro w _
      by_cases hw : ClosedTrail X w
      · simp only [hw, ite_true, ← Finset.mul_sum]
        congr 1
        simp_rw [← exposure_sum]
      · simp [hw]

lemma closed_exposure_bound {n : ℕ} (X : PairType) (w : DirectionWord n)
    (hw : ClosedTrail X w) :
    trailBaseWeight kernelStart w * exposureSum w
      (fun i => ∑ Y : PairType, ∑ s ∈ Finset.range (n + 2), responseKappa X Y s w i)
      (kernelOrdering w) ≤ (n : ℚ) * responseCap * trailWeight kernelStart kernelIncoming w := by
  let r : Fin n → ℚ := fun i => ∑ Y : PairType, ∑ s ∈ Finset.range (n + 2), responseKappa X Y s w i
  let P : ℚ := ((kernelOrdering w).map fun i => passageFactor (wordStraight kernelIncoming w i)).prod
  have hr (i : Fin n) : r i ≤ responseCap := by
    dsimp [r]
    rw [response_total]
    exact pair_sum_cap w hw.1 i
  have hp : 0 ≤ P := by
    apply List.prod_nonneg
    intro x hx
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    exact (show (0 : ℚ) ≤ 1 by norm_num).trans (factor_one_le _)
  have hlen : ((kernelOrdering w).length : ℚ) ≤ (n : ℚ) := by exact_mod_cast ordering_length w
  have he : exposureSum w r (kernelOrdering w) ≤ (n : ℚ) * responseCap * P :=
    (exposure_cap w r hr _).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hlen (by norm_num [responseCap])) hp)
  calc
    _ ≤ trailBaseWeight kernelStart w * ((n : ℚ) * responseCap * P) :=
      mul_le_mul_of_nonneg_left he (base_nonneg w)
    _ = _ := by rw [← ordering_product w]; dsimp [P]; ring

lemma coefficient_mass_bound (CV q : ℝ) (hOpen : OpenTrailBound CV q) (X : PairType) (n : ℕ) :
    (∑ Y : PairType, ∑ s ∈ Finset.range (n + 2), (kernelLengthCoefficient X Y s n : ℝ)) ≤
      (n : ℝ) * (responseCap : ℝ) * CV * q^n := by
  have hrat : (∑ Y : PairType, ∑ s ∈ Finset.range (n + 2), kernelLengthCoefficient X Y s n) ≤
      (n : ℚ) * responseCap *
        (∑ w : DirectionWord n, if IsTrail kernelStart kernelIncoming w then trailWeight kernelStart kernelIncoming w else 0) := by
    rw [coefficient_total, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro w _
    by_cases hw : ClosedTrail X w
    · simp only [hw, hw.1, ite_true]
      exact closed_exposure_bound X w hw
    · simp only [hw, ite_false]
      apply mul_nonneg (mul_nonneg (Nat.cast_nonneg n) (by norm_num [responseCap]))
      split_ifs
      · exact AKLT.Cert.H2.weight_nonneg _ _ _
      · rfl
  have hreal : (∑ Y : PairType, ∑ s ∈ Finset.range (n + 2), (kernelLengthCoefficient X Y s n : ℝ)) ≤
      (n : ℝ) * (responseCap : ℝ) *
        (∑ w : DirectionWord n, if IsTrail kernelStart kernelIncoming w then (trailWeight kernelStart kernelIncoming w : ℝ) else 0) := by
    simpa only [Rat.cast_sum, Rat.cast_mul, Rat.cast_natCast, apply_ite, Rat.cast_zero] using
      ((Rat.cast_le (K := ℝ)).mpr hrat)
  calc
    _ ≤ _ := hreal
    _ ≤ (n : ℝ) * (responseCap : ℝ) * (CV * q^n) :=
      mul_le_mul_of_nonneg_left (hOpen.2.2.2 n kernelStart kernelIncoming)
        (mul_nonneg (Nat.cast_nonneg n) (by norm_num [responseCap]))
    _ = _ := by ring

lemma witness_ratio_bound (X Y : PairType) : witnessReal Y ≤ witnessRatio * witnessReal X := by
  cases X <;> cases Y <;> norm_num [witnessRatio, witnessReal, kernelWitness]

lemma weighted_mass_bound (CV q : ℝ) (hOpen : OpenTrailBound CV q) (X : PairType) (n : ℕ) :
    (∑ Y : PairType, ∑ s ∈ Finset.range (n + 2),
      (kernelLengthCoefficient X Y s n : ℝ) * witnessReal Y) ≤
      witnessRatio * witnessReal X * ((n : ℝ) * (responseCap : ℝ) * CV * q^n) := by
  have hcoeff (Y : PairType) (s : ℕ) : 0 ≤ (kernelLengthCoefficient X Y s n : ℝ) := by
    exact_mod_cast coefficient_nonneg X Y s n
  calc
    _ ≤ ∑ Y : PairType, ∑ s ∈ Finset.range (n + 2),
        (kernelLengthCoefficient X Y s n : ℝ) * (witnessRatio * witnessReal X) := by
      apply Finset.sum_le_sum
      intro Y _
      apply Finset.sum_le_sum
      intro s _
      exact mul_le_mul_of_nonneg_left (witness_ratio_bound X Y) (hcoeff Y s)
    _ = witnessRatio * witnessReal X *
        (∑ Y : PairType, ∑ s ∈ Finset.range (n + 2), (kernelLengthCoefficient X Y s n : ℝ)) := by
      simp_rw [← Finset.sum_mul]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (coefficient_mass_bound CV q hOpen X n)
      (mul_nonneg (by norm_num [witnessRatio, witnessReal, kernelWitness]) (witness_positive X).le)

end AKLT.W.REC070
