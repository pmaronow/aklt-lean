import AKLT.Blueprint.Rec.NodesRecursion

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC081

theorem icoVector_unit (j : IcoLetter) : normSq (icoVector j) = 1 := by
  have hs : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hgpos : 0 < goldenRatio + 2 := by
    unfold goldenRatio
    positivity
  have hg : goldenRatio ^ 2 = goldenRatio + 1 := by
    unfold goldenRatio
    nlinarith
  have hr : icoRadius ^ 2 = goldenRatio + 2 := Real.sq_sqrt hgpos.le
  have hr0 : icoRadius ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hgpos)
  rcases j with ⟨a, b, c⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp [icoVector, signValue, normSq, dot, Fin.sum_univ_succ] <;>
    field_simp <;> nlinarith

theorem spinVector_ball (j : SpinLetter) : normSq (spinVector j) ≤ 1 := by
  cases j with
  | none => norm_num [spinVector, normSq, dot]
  | some j => exact (icoVector_unit j).le

theorem interaction_nonneg (a b : Vec3) (ha : normSq a ≤ 1) (hb : normSq b ≤ 1) :
    0 ≤ 1 + dot a b := by
  have hsum : 0 ≤ ∑ i : Fin 3, (a i + b i)^2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have heq : (∑ i : Fin 3, (a i + b i)^2) = normSq a + 2 * dot a b + normSq b := by
    simp [normSq, dot, Fin.sum_univ_succ]
    ring
  rw [heq] at hsum
  linarith

theorem spinWeight_nonneg (s : Status) (j : SpinLetter) : 0 ≤ spinWeight s j := by
  cases s <;> cases j <;> norm_num [spinWeight]

theorem network_spins_ball {G : Finset Plane} (D : Network G)
    (n : (x : D.active) → SpinLetter) (x : Plane) : normSq (D.spins n x) ≤ 1 := by
  classical
  unfold Network.spins
  split
  · exact spinVector_ball _
  · norm_num [normSq, dot]

/-- Nonnegativity needs no strict-positivity or admissibility premise. -/
theorem network_normalizer_nonneg {G : Finset Plane} (D : Network G)
    (τ : PinAssignment G) (b : Bool) : 0 ≤ D.partition τ b (fun _ => 1) := by
  classical
  unfold Network.partition
  apply Finset.sum_nonneg
  intro n _
  apply mul_nonneg
  · apply mul_nonneg
    · apply mul_nonneg
      · exact Finset.prod_nonneg (fun _ _ => spinWeight_nonneg _ _)
      · norm_num
    · exact Finset.prod_nonneg (fun e _ => interaction_nonneg _ _
        (network_spins_ball D n e.1) (network_spins_ball D n e.2))
  · apply Finset.prod_nonneg
    intro e _
    split
    · exact interaction_nonneg _ _ (τ e).property.le (network_spins_ball D n e.val.1)
    · norm_num

theorem traceRatio_nonneg {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (w : List Plane) : 0 ≤ traceRatio D τ b w :=
  div_nonneg (network_normalizer_nonneg _ _ _) (network_normalizer_nonneg _ _ _)

theorem traceCoefficient_nonneg {G : Finset Plane} (D : Network G) (w : List Plane) :
    0 ≤ traceCoefficient D w := by
  induction w generalizing D with
  | nil => norm_num [traceCoefficient]
  | cons y rest ih =>
    cases rest with
    | nil => norm_num [traceCoefficient]
    | cons o rest =>
      simp only [traceCoefficient]
      apply mul_nonneg _ (ih (traceStep D y o))
      split_ifs <;> norm_num

theorem traceCoefficient_cast_nonneg {G : Finset Plane} (D : Network G) (w : List Plane) :
    (0 : ℝ) ≤ (traceCoefficient D w : ℝ) := by
  exact_mod_cast traceCoefficient_nonneg D w

theorem trace_max_nonneg {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (w : List Plane) : 0 ≤ max (traceRatio D τ true w) (traceRatio D τ false w) :=
  (traceRatio_nonneg D τ true w).trans (le_max_left _ _)

end AKLT.W.REC081
