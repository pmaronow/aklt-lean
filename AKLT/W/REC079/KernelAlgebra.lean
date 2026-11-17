module
public import AKLT.W.REC079.Geometry

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators ENNReal
open AKLT.Defs AKLT.Blueprint.Rec AKLT.Cert.H2

namespace AKLT.W.REC079

attribute [local instance] Classical.propDecidable

/-- Exposure with real rewards and the frozen rational passage factors. -/
def realExposure {n : ℕ} (w : DirectionWord n) (r : Fin n → ℝ) : List (Fin n) → ℝ
  | [] => 0
  | i :: rest => (passageFactor (wordStraight kernelIncoming w i) : ℝ) *
      (r i + realExposure w r rest)

@[simp] theorem realExposure_cast {n : ℕ} (w : DirectionWord n) (r : Fin n → ℚ)
    (l : List (Fin n)) :
    realExposure w (fun i => (r i : ℝ)) l = (exposureSum w r l : ℝ) := by
  induction l with
  | nil => simp [realExposure, exposureSum]
  | cons i l ih => simp [realExposure, exposureSum, ih]

theorem realExposure_sum {n : ℕ} (w : DirectionWord n) {ι : Type*} (s : Finset ι)
    (r : ι → Fin n → ℝ) (l : List (Fin n)) :
    realExposure w (fun i => ∑ a ∈ s, r a i) l =
      ∑ a ∈ s, realExposure w (r a) l := by
  induction l with
  | nil => simp [realExposure]
  | cons i l ih => simp [realExposure, ih, ← Finset.sum_add_distrib, Finset.mul_sum]

theorem realExposure_mul {n : ℕ} (w : DirectionWord n) (r : Fin n → ℝ) (c : ℝ)
    (l : List (Fin n)) :
    realExposure w (fun i => r i * c) l = realExposure w r l * c := by
  induction l with
  | nil => simp [realExposure]
  | cons i l ih => simp only [realExposure, ih]; ring

theorem realExposure_nonneg {n : ℕ} (w : DirectionWord n) (r : Fin n → ℝ)
    (hr : ∀ i, 0 ≤ r i) (l : List (Fin n)) : 0 ≤ realExposure w r l := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    apply mul_nonneg _ (add_nonneg (hr i) ih)
    cases h : wordStraight kernelIncoming w i <;> norm_num [passageFactor, localThreshold]

theorem realExposure_mono {n : ℕ} (w : DirectionWord n) (r r' : Fin n → ℝ)
    (hr : ∀ i, r i ≤ r' i) (l : List (Fin n)) :
    realExposure w r l ≤ realExposure w r' l := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    apply mul_le_mul_of_nonneg_left (add_le_add (hr i) ih)
    cases h : wordStraight kernelIncoming w i <;> norm_num [passageFactor, localThreshold]

/-- Inserting the extra lattice first visits into an exposure order can only
increase a nonnegative reward sum, since every passage factor is at least one. -/
theorem realExposure_filter_le {n : ℕ} (w : DirectionWord n) (r : Fin n → ℝ)
    (hr : ∀ i, 0 ≤ r i) (keep : Fin n → Bool) (l : List (Fin n)) :
    realExposure w r (l.filter keep) ≤ realExposure w r l := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    have hx : (1 : ℝ) ≤ (passageFactor (wordStraight kernelIncoming w i) : ℝ) := by
      cases h : wordStraight kernelIncoming w i <;> norm_num [passageFactor, localThreshold]
    by_cases hi : keep i = true
    · simp only [List.filter_cons_of_pos hi, realExposure]
      exact mul_le_mul_of_nonneg_left (add_le_add (le_refl _) ih) (by linarith)
    · simp only [List.filter_cons_of_neg hi, realExposure]
      apply ih.trans
      have he := realExposure_nonneg w r hr l
      nlinarith [hr i]

/-- The finite type/shift reward at one departure. The cutoff is the exact
one in the frozen statement. -/
def indexedReward {n : ℕ} (X : PairType) (d : ℕ) (w : DirectionWord n) (i : Fin n) : ℝ :=
  ∑ Y : PairType, ∑ s ∈ Finset.range (n + 2),
    (responseKappa X Y s w i : ℝ) * responseEnvelope Y ((d : ℤ) - s)

/-- A single canonical trail's contribution to the frozen bound. -/
def canonicalBudget {n : ℕ} (X : PairType) (d : ℕ) (w : DirectionWord n) : ℝ :=
  (trailBaseWeight kernelStart w : ℝ) *
    realExposure w (indexedReward X d w) (kernelOrdering w)

/-- The full finite coefficient sum is exactly the sum of canonical trail
budgets. No interchange of infinite or conditionally convergent sums occurs. -/
theorem kernel_bound_eq_sum (X : PairType) (d n : ℕ) :
    (∑ Y : PairType, ∑ s ∈ Finset.range (n + 2),
      (kernelLengthCoefficient X Y s n : ℝ) * responseEnvelope Y ((d : ℤ) - s)) =
    ∑ w : DirectionWord n, if ClosedTrail X w then canonicalBudget X d w else 0 := by
  classical
  simp only [kernelLengthCoefficient, Rat.cast_sum, apply_ite, Rat.cast_mul,
    Rat.cast_zero, Finset.sum_mul]
  simp_rw [Finset.sum_comm (s := Finset.range (n + 2))
    (t := (Finset.univ : Finset (DirectionWord n)))]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  by_cases hw : ClosedTrail X w
  · simp only [hw, ite_true, canonicalBudget]
    unfold indexedReward
    rw [realExposure_sum]
    simp_rw [realExposure_sum, realExposure_mul, realExposure_cast]
    simp_rw [Finset.mul_sum, mul_assoc]
  · simp [hw]

end AKLT.W.REC079
