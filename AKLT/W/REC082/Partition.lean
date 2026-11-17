module
public import AKLT.W.REC082.Moments

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators ENNReal
open AKLT.Defs AKLT.Blueprint.Rec

namespace AKLT.W.REC082

theorem normSq_nonneg (a : Vec3) : 0 ≤ normSq a := by
  unfold normSq dot
  exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (a i))

theorem normSq_add (a b : Vec3) : normSq (a + b) = normSq a + 2 * dot a b + normSq b := by
  simp only [normSq, dot, Pi.add_apply, Fin.sum_univ_succ]
  ring

theorem ball_factor_nonneg (a b : Vec3) (ha : normSq a ≤ 1) (hb : normSq b ≤ 1) :
    0 ≤ 1 + dot a b := by
  have h := normSq_nonneg (a + b)
  rw [normSq_add] at h
  linarith

theorem spins_ball {G : Finset Plane} (D : Network G)
    (n : (x : D.active) → SpinLetter) (x : Plane) : normSq (D.spins n x) ≤ 1 := by
  unfold Network.spins
  split_ifs
  · exact spinVector_ball _
  · norm_num [normSq, dot]

/-- The finite nonnegative weight, separating the observable from the partition. -/
def partitionWeight {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (n : (x : D.active) → SpinLetter) : ℝ :=
  (∏ x : D.active, spinWeight (D.status x.val) (n x)) *
    (∏ e ∈ D.bonds, (1 + dot (D.spins n e.1) (D.spins n e.2))) *
    ∏ e : originalLegs G,
      if b = true ∧ e.val.1 ∈ D.active then
        1 + dot (τ e).val (D.spins n e.val.1) else 1

theorem partition_eq_sum_weight {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (f : (Plane → Vec3) → ℝ) :
    D.partition τ b f = ∑ n, partitionWeight D τ b n * f (D.spins n) := by
  unfold Network.partition partitionWeight
  apply Finset.sum_congr rfl
  intro n _
  ring

theorem partitionWeight_nonneg {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (n : (x : D.active) → SpinLetter) : 0 ≤ partitionWeight D τ b n := by
  apply mul_nonneg
  · apply mul_nonneg
    · exact Finset.prod_nonneg (fun x _ => spinWeight_nonneg _ _)
    · exact Finset.prod_nonneg (fun e _ => ball_factor_nonneg _ _ (spins_ball D n _)
        (spins_ball D n _))
  · apply Finset.prod_nonneg
    intro e _
    split_ifs
    · exact ball_factor_nonneg _ _ (le_of_eq (τ e).property) (spins_ball D n _)
    · exact zero_le_one

/-- Zero mass forces every weighted observable to vanish. This also handles
normalization algebra without assuming a strictly positive denominator. -/
theorem partition_zero_of_mass_zero {G : Finset Plane} (D : Network G)
    (τ : PinAssignment G) (b : Bool) (h : D.partition τ b (fun _ => 1) = 0)
    (f : (Plane → Vec3) → ℝ) : D.partition τ b f = 0 := by
  classical
  rw [partition_eq_sum_weight] at h ⊢
  simp only [mul_one] at h
  have hz := (Finset.sum_eq_zero_iff_of_nonneg
    (fun n _ => partitionWeight_nonneg D τ b n)).mp h
  exact Finset.sum_eq_zero (fun n hn => by rw [hz n hn, zero_mul])

/-- A traced expectation times its partition ratio is its numerator divided by
just the original mass, including either possible zero denominator. -/
theorem traceRatio_mul_expectation {G : Finset Plane} (D : Network G)
    (τ : PinAssignment G) (b : Bool) (w : List Plane) (f : (Plane → Vec3) → ℝ) :
    traceRatio D τ b w * (traceNetwork D w).expectation τ b f =
      (traceNetwork D w).partition τ b f / D.partition τ b (fun _ => 1) := by
  classical
  unfold traceRatio Network.expectation
  by_cases h : (traceNetwork D w).partition τ b (fun _ => 1) = 0
  · rw [partition_zero_of_mass_zero _ τ b h f, h]
    simp
  · field_simp

/-- An identity of terminal numerators gives exactly the weighted terminal
factor needed when subtracting the two expansions. -/
theorem traceRatio_mul_terminal_of_partition {G : Finset Plane} (D : Network G)
    (τ : PinAssignment G) (b : Bool) (w : List Plane) (v : Plane) (η : ℝ)
    (h : (traceNetwork D w).partition τ b (fun a => normSq (a v)) =
      η * (traceNetwork D w).partition τ b (fun _ => 1)) :
    traceRatio D τ b w * (traceNetwork D w).expectation τ b (fun a => normSq (a v)) =
      traceRatio D τ b w * η := by
  rw [traceRatio_mul_expectation, h]
  unfold traceRatio
  ring

end AKLT.W.REC082
