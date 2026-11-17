module
public import AKLT.W.REC021.LogMean
public import AKLT.W.REC021.DepartureBound

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC021

theorem beta_of_I_lower {x y : ℝ} (hx : (41 / 50 : ℝ) ≤ x) (hy : 1 ≤ y) :
    1 / (3 * logarithmicMean x y) ≤ (36751 / 100000 : ℝ) := by
  have hxp : 0 < x := by linarith
  have hyp : 0 < y := by linarith
  have hLmLow : logarithmicMean (41 / 50 : ℝ) 1 ≤ logarithmicMean x y :=
    logarithmicMean_monotone _ _ _ _ (by norm_num) hx (by norm_num) hy
  have hLmPos := logarithmicMean_pos_local hxp hyp
  have hLm41Pos : 0 < logarithmicMean (41 / 50 : ℝ) 1 :=
    logarithmicMean_pos_local (by norm_num) (by norm_num)
  have hInv : (logarithmicMean x y)⁻¹ ≤ (logarithmicMean (41 / 50 : ℝ) 1)⁻¹ :=
    (inv_le_inv₀ hLmPos hLm41Pos).2 hLmLow
  have hCrude : reciprocalLogMean (41 / 50 : ℝ) / 3 ≤ (367502 / 10^6 : ℝ) := by
    calc
      reciprocalLogMean (41 / 50 : ℝ) / 3 ≤
          (AKLT.Blueprint.Rec.crudeLogUpper (41 / 50) : ℝ) / 3 :=
        div_le_div_of_nonneg_right crudeLogAt41 (by norm_num)
      _ ≤ (367502 / 10^6 : ℝ) := by
        norm_num [AKLT.Blueprint.Rec.crudeLogUpper]
  calc
    1 / (3 * logarithmicMean x y) = (logarithmicMean x y)⁻¹ / 3 := by ring
    _ ≤ (logarithmicMean (41 / 50 : ℝ) 1)⁻¹ / 3 :=
      div_le_div_of_nonneg_right hInv (by norm_num)
    _ = reciprocalLogMean (41 / 50 : ℝ) / 3 := rfl
    _ ≤ (367502 / 10^6 : ℝ) := hCrude
    _ ≤ (36751 / 100000 : ℝ) := by norm_num

/-- The uniform three-neighbor beta bound, with no residual assumptions. -/
theorem main : AKLT.Blueprint.Rec.BetaUniformStatement := by
  intro a hU f g hN hof hog hfg
  exact beta_of_I_lower (responseI_pinned_lower_closed a f g hN hof hog hfg)
    (responseI_free_lower a.D a.τ a.y a.o f g)

#print axioms beta_of_I_lower
#print axioms main

end AKLT.W.REC021
