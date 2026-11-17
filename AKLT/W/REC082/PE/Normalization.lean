module
public import AKLT.W.REC082.PE.Moments

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC082.PE

private theorem one_add_dot_nonneg {a b : Vec3}
    (ha : normSq a ≤ 1) (hb : normSq b ≤ 1) : 0 ≤ 1 + dot a b := by
  have hs : 0 ≤ ∑ i : Fin 3, (a i + b i) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have he : (∑ i : Fin 3, (a i + b i) ^ 2) = normSq a + normSq b + 2 * dot a b := by
    simp only [normSq, dot, Fin.sum_univ_three]
    ring
  rw [he] at hs
  linarith

private theorem spin_weight_nonneg (s : Status) (j : SpinLetter) :
    0 ≤ spinWeight s j := by
  cases s <;> cases j <;> norm_num [spinWeight]

private theorem spins_norm_le {G : Finset Plane} (D : Network G)
    (n : (x : D.active) → SpinLetter) (x : Plane) : normSq (D.spins n x) ≤ 1 := by
  unfold Network.spins
  split_ifs
  · exact spin_norm_le _
  · norm_num [normSq, dot]

/-- The configuration weight, with the observable removed. -/
def configurationWeight {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (n : (x : D.active) → SpinLetter) : ℝ :=
  (∏ x : D.active, spinWeight (D.status x.val) (n x)) *
    (∏ e ∈ D.bonds, (1 + dot (D.spins n e.1) (D.spins n e.2))) *
      ∏ e : originalLegs G, if b = true ∧ e.val.1 ∈ D.active then
        1 + dot (τ e).val (D.spins n e.val.1) else 1

/-- Nonnegativity holds even without auxiliary validity. -/
theorem configurationWeight_nonneg {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (n : (x : D.active) → SpinLetter) : 0 ≤ configurationWeight D τ b n := by
  apply mul_nonneg
  · apply mul_nonneg
    · exact Finset.prod_nonneg fun x _ => spin_weight_nonneg _ _
    · exact Finset.prod_nonneg fun e _ => one_add_dot_nonneg (spins_norm_le _ _ _)
        (spins_norm_le _ _ _)
  · apply Finset.prod_nonneg
    intro e he
    split_ifs
    · exact one_add_dot_nonneg (τ e).property.le (spins_norm_le _ _ _)
    · norm_num

theorem partition_eq_weighted_sum {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (f : (Plane → Vec3) → ℝ) :
    D.partition τ b f = ∑ n, configurationWeight D τ b n * f (D.spins n) := by
  classical
  unfold Network.partition configurationWeight
  apply Finset.sum_congr rfl
  intro n hn
  ring

/-- A zero normalizer forces every observable numerator to vanish. This
allows normalization at the very end without a separate strict-positivity input. -/
theorem partition_zero_of_normalizer_zero {G : Finset Plane} (D : Network G)
    (τ : PinAssignment G) (b : Bool) (hZ : D.partition τ b (fun _ => 1) = 0)
    (f : (Plane → Vec3) → ℝ) : D.partition τ b f = 0 := by
  classical
  have hsum : (∑ n, configurationWeight D τ b n) = 0 := by
    simpa only [partition_eq_weighted_sum, mul_one] using hZ
  have hw (n : (x : D.active) → SpinLetter) : configurationWeight D τ b n = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun m _ => configurationWeight_nonneg D τ b m)).mp
      hsum n (Finset.mem_univ _)
  rw [partition_eq_weighted_sum]
  apply Finset.sum_eq_zero
  intro n hn
  rw [hw, zero_mul]

/-- Cancellation remains valid at a zero normalizer, since its numerator is zero. -/
theorem normalizer_mul_expectation {G : Finset Plane} (D : Network G)
    (τ : PinAssignment G) (b : Bool) (f : (Plane → Vec3) → ℝ) :
    D.partition τ b (fun _ => 1) * D.expectation τ b f = D.partition τ b f := by
  unfold Network.expectation
  by_cases hZ : D.partition τ b (fun _ => 1) = 0
  · rw [hZ, zero_mul, partition_zero_of_normalizer_zero D τ b hZ f]
  · field_simp

end AKLT.W.REC082.PE
