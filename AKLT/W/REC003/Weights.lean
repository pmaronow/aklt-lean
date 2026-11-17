import AKLT.W.REC003.Moments
import AKLT.Defs.Domain

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC003

theorem spin_weight_nonneg (s : Status) (j : SpinLetter) : 0 ≤ spinWeight s j := by
  cases s <;> cases j <;> norm_num [spinWeight]

theorem spins_ball {G : Finset Plane} (D : Network G)
    (n : D.active → SpinLetter) (x : Plane) : normSq (D.spins n x) ≤ 1 := by
  unfold Network.spins
  split_ifs
  · exact spin_ball _
  · norm_num [normSq, dot]

def partitionWeight {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (n : D.active → SpinLetter) : ℝ :=
  (∏ x : D.active, spinWeight (D.status x) (n x)) *
    (∏ e ∈ D.bonds, (1 + dot (D.spins n e.1) (D.spins n e.2))) *
      ∏ e : originalLegs G,
        if b = true ∧ e.val.1 ∈ D.active then
          1 + dot (τ e).val (D.spins n e.val.1) else 1

theorem partition_eq_sum {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (f : (Plane → Vec3) → ℝ) :
    D.partition τ b f = ∑ n, partitionWeight D τ b n * f (D.spins n) := by
  unfold Network.partition partitionWeight
  apply Finset.sum_congr rfl
  intro n _
  ring

theorem partitionWeight_nonneg {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (n : D.active → SpinLetter) : 0 ≤ partitionWeight D τ b n := by
  apply mul_nonneg
  · apply mul_nonneg
    · exact Finset.prod_nonneg fun x _ => spin_weight_nonneg _ _
    · exact Finset.prod_nonneg fun e _ =>
        factor_nonneg _ _ (spins_ball D n _) (spins_ball D n _)
  · apply Finset.prod_nonneg
    intro e _
    split_ifs
    · exact factor_nonneg _ _ (τ e).property.le (spins_ball D n _)
    · norm_num

/-- A zero total mass has no nonzero atoms, so every inserted partition vanishes. -/
theorem partition_zero {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (hz : D.partition τ b (fun _ => 1) = 0)
    (f : (Plane → Vec3) → ℝ) : D.partition τ b f = 0 := by
  rw [partition_eq_sum] at hz ⊢
  simp only [mul_one] at hz
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg
    (fun n _ => partitionWeight_nonneg D τ b n)).mp hz
  apply Finset.sum_eq_zero
  intro n hn
  rw [hzero n hn, zero_mul]

theorem partition_mul_expectation {G : Finset Plane} (D : Network G)
    (τ : PinAssignment G) (b : Bool) (f : (Plane → Vec3) → ℝ) :
    D.partition τ b (fun _ => 1) * D.expectation τ b f = D.partition τ b f := by
  unfold Network.expectation
  by_cases hz : D.partition τ b (fun _ => 1) = 0
  · rw [hz, zero_mul, partition_zero D τ b hz f]
  · exact mul_div_cancel₀ _ hz

theorem partition_add {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (f g : (Plane → Vec3) → ℝ) :
    D.partition τ b (fun n => f n + g n) = D.partition τ b f + D.partition τ b g := by
  simp only [partition_eq_sum, mul_add, Finset.sum_add_distrib]

theorem partition_div {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (f : (Plane → Vec3) → ℝ) (c : ℝ) :
    D.partition τ b (fun n => f n / c) = D.partition τ b f / c := by
  simp only [partition_eq_sum, mul_div_assoc, Finset.sum_div]

end AKLT.W.REC003
