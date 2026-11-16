import AKLT.W.REC019.SpinGeometry

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC019

theorem network_spins_ball {G : Finset Plane} (D : Network G)
    (σ : D.active → SpinLetter) (x : Plane) : normSq (D.spins σ x) ≤ 1 := by
  by_cases hx : x ∈ D.active
  · simpa only [Network.spins, dite_eq_left hx] using spinVector_ball (σ ⟨x, hx⟩)
  · simp [Network.spins, hx, normSq, dot]

def networkWeight {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (σ : D.active → SpinLetter) : ℝ :=
  (∏ x : D.active, spinWeight (D.status x.val) (σ x)) *
    (∏ e ∈ D.bonds, (1 + dot (D.spins σ e.1) (D.spins σ e.2))) *
    ∏ e : originalLegs G,
      if b = true ∧ e.val.1 ∈ D.active then
        1 + dot (τ e).val (D.spins σ e.val.1) else 1

theorem partition_as_weight {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (f : (Plane → Vec3) → ℝ) :
    D.partition τ b f = ∑ σ : D.active → SpinLetter, networkWeight D τ b σ * f (D.spins σ) := by
  unfold Network.partition networkWeight
  apply Finset.sum_congr rfl
  intro σ hσ
  ring

theorem networkWeight_nonnegative {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (σ : D.active → SpinLetter) : 0 ≤ networkWeight D τ b σ := by
  unfold networkWeight
  apply mul_nonneg
  · apply mul_nonneg
    · exact Finset.prod_nonneg fun x hx => spinWeight_nonnegative _ _
    · apply Finset.prod_nonneg
      intro e he
      have h := (dot_ball_bounds (network_spins_ball D σ e.1) (network_spins_ball D σ e.2)).1
      linarith
  · apply Finset.prod_nonneg
    intro e he
    split_ifs with h
    · have hd := (dot_ball_bounds (τ e).property.le (network_spins_ball D σ e.val.1)).1
      linarith
    · norm_num

theorem network_partition_nonnegative {G : Finset Plane} (D : Network G)
    (τ : PinAssignment G) (b : Bool) : 0 ≤ D.partition τ b (fun _ => 1) := by
  rw [partition_as_weight]
  simp only [mul_one]
  exact Finset.sum_nonneg fun σ hσ => networkWeight_nonnegative _ _ _ _

/-- This also covers a zero normalizer: the definitions use the real quotient. -/
theorem network_pair_expectation_bounds {G : Finset Plane} (D : Network G)
    (τ : PinAssignment G) (b : Bool) (x y : Plane) :
    -1 ≤ D.expectation τ b (fun n => dot (n x) (n y)) ∧
      D.expectation τ b (fun n => dot (n x) (n y)) ≤ 1 := by
  let Z := D.partition τ b (fun _ => 1)
  let N := D.partition τ b (fun n => dot (n x) (n y))
  have hZ : 0 ≤ Z := network_partition_nonnegative _ _ _
  have hN : -Z ≤ N ∧ N ≤ Z := by
    dsimp [Z, N]
    simp only [partition_as_weight, mul_one]
    constructor
    · rw [← Finset.sum_neg_distrib]
      apply Finset.sum_le_sum
      intro σ hσ
      have hd := (dot_ball_bounds (network_spins_ball D σ x) (network_spins_ball D σ y)).1
      have h := mul_le_mul_of_nonneg_left hd (networkWeight_nonnegative D τ b σ)
      simpa only [mul_neg, mul_one] using h
    · apply Finset.sum_le_sum
      intro σ hσ
      have hd := (dot_ball_bounds (network_spins_ball D σ x) (network_spins_ball D σ y)).2
      have h := mul_le_mul_of_nonneg_left hd (networkWeight_nonnegative D τ b σ)
      simpa only [mul_one] using h
  change -1 ≤ N / Z ∧ N / Z ≤ 1
  by_cases hz : Z = 0
  · simp [hz]
  · have hz' : 0 < Z := lt_of_le_of_ne hZ (Ne.symm hz)
    constructor
    · apply (le_div_iff₀ hz').mpr
      simpa using hN.1
    · exact (div_le_one hz').mpr hN.2

theorem responseJ_positive {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (y f g : Plane) : 0 < responseJ D τ b y f g := by
  have h := (network_pair_expectation_bounds (removeSite D y) τ b f g).1
  unfold responseJ removedPairMean
  linarith

end AKLT.W.REC019
