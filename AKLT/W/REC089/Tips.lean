module
public import AKLT.W.REC089.Slots

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC089

/-- A tip has three external directions, padded by zero fields when absent. -/
def tipExternal (b : Fin 3 → Vec3) (n : Vec3) : ℝ := ∏ j, (1 + dot n (b j))

def tipValue (s : Status) (bond : Bool) (b : Fin 3 → Vec3) (v : Vec3) : ℝ :=
  if s = .X then 1 else
    siteFunctional s (fun n => (if bond then 1 + dot n v else 1) * tipExternal b n)

def coveredTipValue (bond : Bool) (b : Fin 3 → Vec3) (v : Vec3) : ℝ :=
  siteFunctional .U (fun n => (if bond then 1 + dot n v else 1) * tipExternal b n)

theorem neutral_tip (bond : Bool) (v : Vec3) :
    coveredTipValue bond (fun _ => 0) v = 1 := by
  cases bond
  · simpa [coveredTipValue, tipExternal, dot_zero_right] using site_U_mass
  · simpa [coveredTipValue, tipExternal, dot_zero_right] using site_U_affine v

theorem tip_normalizer_nonneg (s : Status) (b : Fin 3 → Vec3)
    (hb : ∀ j, normSq (b j) ≤ 1) :
    0 ≤ siteFunctional s (tipExternal b) := by
  apply Finset.sum_nonneg
  intro n _
  apply mul_nonneg (spinWeight_nonneg s n)
  unfold tipExternal
  exact Finset.prod_nonneg fun j _ => ball_factor_nonneg _ _ (spin_ball n) (hb j)

/-- Two branches suffice: the U part and the zero part of the D law.
For an absent actual bond all of its external normalizer is a scalar. -/
theorem tip_ball_mixture (s : Status) (actual cover : Bool)
    (hkeep : actual = true → cover = true)
    (hlive : actual = true → s ≠ .X)
    (b : Fin 3 → Vec3) (hb : ∀ j, normSq (b j) ≤ 1) :
    ∃ fields : Bool → Fin 3 → Vec3, ∃ w : Bool → ℝ,
      (∀ q, 0 ≤ w q) ∧ (∀ q j, normSq (fields q j) ≤ 1) ∧
      ∀ v : Vec3, tipValue s actual b v =
        ∑ q : Bool, w q * coveredTipValue cover (fields q) v := by
  classical
  cases ha : actual with
  | false =>
    let A : ℝ := if s = .X then 1 else siteFunctional s (tipExternal b)
    refine ⟨fun _ _ => 0, (fun q => if q then A else 0), ?_, ?_, ?_⟩
    · intro q
      cases q <;> simp [A]
      split_ifs
      · norm_num
      · exact tip_normalizer_nonneg s b hb
    · intro q j
      norm_num [normSq, dot]
    · intro v
      simp [tipValue, ha, A, Fintype.sum_bool, neutral_tip]
  | true =>
    have hc : cover = true := hkeep ha
    have hx : s ≠ .X := hlive ha
    refine ⟨(fun q j => if q then b j else 0),
      (fun q => if q then (if s = .U then 1 else 3 / 5)
        else (if s = .U then 0 else 2 / 5)), ?_, ?_, ?_⟩
    · intro q
      cases q <;> split_ifs <;> norm_num
    · intro q j
      cases q
      · norm_num [normSq, dot]
      · exact hb j
    · intro v
      cases s with
      | X => exact (hx rfl).elim
      | U => simp [tipValue, coveredTipValue, hc, ha, Fintype.sum_bool]
      | D =>
        rw [tipValue, if_neg (by decide), site_D_split]
        simp only [ha, Bool.true_eq, if_true, Fintype.sum_bool, Bool.false_eq_true,
          if_false, Status.noConfusion, neutral_tip, hc]
        simp [coveredTipValue, tipExternal, dot_zero_left]
        <;> ring

#print axioms tip_ball_mixture
#print axioms neutral_tip

end AKLT.W.REC089
