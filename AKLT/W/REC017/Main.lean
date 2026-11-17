module
public import AKLT.W.REC017.Factorization

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open AKLT.Defs AKLT.Blueprint.Rec

namespace AKLT.W.REC017

private theorem log_sub_log_eq_div_logarithmicMean
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.log x - Real.log y = (x - y) / logarithmicMean x y := by
  unfold logarithmicMean
  rcases lt_trichotomy x y with hxy | hxy | hyx
  · rw [ite_eq_right (ne_of_lt hxy)]
    have hlog : Real.log x ≠ Real.log y :=
      ne_of_lt (Real.log_lt_log hx hxy)
    have hnum : x - y ≠ 0 := ne_of_lt (sub_neg.mpr hxy)
    field_simp [hlog, hnum]
  · subst y
    simp
  · rw [ite_eq_right (ne_of_gt hyx)]
    have hlog : Real.log x ≠ Real.log y :=
      ne_of_gt (Real.log_lt_log hy hyx)
    have hnum : x - y ≠ 0 := ne_of_gt (sub_pos.mpr hyx)
    field_simp [hlog, hnum]

/-- The exact two-neighbour logarithmic response, including coincident I₂ values. -/
theorem main : AKLT.Blueprint.Rec.TwoLogIdentityStatement := by
  intro a hU f hN hne
  rw [log_stepRatio a hU f hN hne false, log_stepRatio a hU f hN hne true]
  calc
    -Real.log (responseI₂ a.D a.τ false a.y a.o f) -
        -Real.log (responseI₂ a.D a.τ true a.y a.o f) =
        Real.log (responseI₂ a.D a.τ true a.y a.o f) -
          Real.log (responseI₂ a.D a.τ false a.y a.o f) := by ring
    _ = (responseI₂ a.D a.τ true a.y a.o f - responseI₂ a.D a.τ false a.y a.o f) /
        logarithmicMean (responseI₂ a.D a.τ true a.y a.o f)
          (responseI₂ a.D a.τ false a.y a.o f) :=
      log_sub_log_eq_div_logarithmicMean
        (responseI₂_pos a.D a.τ true a.y a.o f) (responseI₂_pos a.D a.τ false a.y a.o f)
    _ = responseBetaPrime a.D a.τ a.y a.o f * pairResponse a.D a.τ a.y f a.o := by
      unfold responseI₂ responseBetaPrime pairResponse
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

#print axioms main

end AKLT.W.REC017
