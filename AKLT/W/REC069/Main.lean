module
public import AKLT.Blueprint.Rec.NodesKernel

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section

open AKLT.Defs

namespace AKLT.W.REC069

/-- The explicit epsilon choice from the transport estimate. -/
theorem main : AKLT.Blueprint.Rec.TransportChoiceStatement := by
  intro CV q hOpen
  rcases hOpen with ⟨hCV, hq0, hq1, _⟩
  let b : ℝ := (1 + q) / 2
  let r : ℝ := q / b
  have hbq : q < b := by dsimp [b]; linarith
  have hb1 : b < 1 := by dsimp [b]; linarith
  have hb0 : 0 < b := lt_trans hq0 hbq
  have hr0 : 0 < r := div_pos hq0 hb0
  have hr1 : r < 1 := by
    dsimp [r]
    rw [div_lt_one hb0]
    exact hbq
  have hratio : 0 < AKLT.Blueprint.Rec.witnessRatio := by
    unfold AKLT.Blueprint.Rec.witnessRatio
    apply div_pos
    · exact lt_of_lt_of_le (AKLT.Blueprint.Rec.witness_positive .B)
        (le_max_left _ _)
    · apply lt_min
      · exact AKLT.Blueprint.Rec.witness_positive .B
      · exact AKLT.Blueprint.Rec.witness_positive .C
  have hcoef : 0 < (18094 / 100000 + 2 * (36751 / 100000 : ℝ)) := by norm_num
  have hCV0 : 0 < CV := lt_of_lt_of_le (by norm_num) hCV
  have hB : 0 < AKLT.Blueprint.Rec.transportB CV q := by
    have hden : 0 < 1 - r := sub_pos.mpr hr1
    have hformula : 0 <
        2 * AKLT.Blueprint.Rec.witnessRatio *
          (18094 / 100000 + 2 * (36751 / 100000 : ℝ)) * CV *
          b ^ (-2 : ℤ) * r / (1 - r) ^ 3 := by
      positivity
    simpa [AKLT.Blueprint.Rec.transportB, b, r] using hformula
  have hrho0 : 0 < (kernelRho : ℝ) := by norm_num [kernelRho]
  have hrho1 : (kernelRho : ℝ) < 1 := by norm_num [kernelRho]
  have heps0 : 0 < AKLT.Blueprint.Rec.transportEpsilon CV q := by
    unfold AKLT.Blueprint.Rec.transportEpsilon
    apply lt_min
    · exact div_pos (sub_pos.mpr hb1) (by norm_num)
    · exact div_pos (sub_pos.mpr hrho1) (mul_pos (by norm_num) hB)
  have hepsleft : AKLT.Blueprint.Rec.transportEpsilon CV q ≤ (1 - b) / 2 := by
    unfold AKLT.Blueprint.Rec.transportEpsilon
    exact min_le_left _ _
  have hepsright : AKLT.Blueprint.Rec.transportEpsilon CV q ≤
      (1 - (kernelRho : ℝ)) / (2 * AKLT.Blueprint.Rec.transportB CV q) := by
    unfold AKLT.Blueprint.Rec.transportEpsilon
    exact min_le_right _ _
  have hbtheta : b < AKLT.Blueprint.Rec.transportTheta CV q := by
    dsimp [AKLT.Blueprint.Rec.transportTheta]
    nlinarith [hepsleft, hb1]
  have hq2q : q ^ 2 < q := by nlinarith [hq0, hq1]
  have hthetaq : q ^ 2 < AKLT.Blueprint.Rec.transportTheta CV q :=
    lt_trans (lt_trans hq2q hbq) hbtheta
  have htheta1 : AKLT.Blueprint.Rec.transportTheta CV q < 1 := by
    dsimp [AKLT.Blueprint.Rec.transportTheta]
    linarith [heps0]
  have hrhotheta : (kernelRho : ℝ) < AKLT.Blueprint.Rec.transportRho := by
    unfold AKLT.Blueprint.Rec.transportRho
    linarith
  have hrho_lt : AKLT.Blueprint.Rec.transportRho < 1 := by
    unfold AKLT.Blueprint.Rec.transportRho
    linarith
  have hbudget : AKLT.Blueprint.Rec.transportEpsilon CV q *
      AKLT.Blueprint.Rec.transportB CV q ≤ (1 - (kernelRho : ℝ)) / 2 := by
    have hden : 0 < 2 * AKLT.Blueprint.Rec.transportB CV q := mul_pos (by norm_num) hB
    have hmul := (le_div_iff₀ hden).mp hepsright
    nlinarith
  have hlast : (kernelRho : ℝ) +
      (1 - AKLT.Blueprint.Rec.transportTheta CV q) *
        AKLT.Blueprint.Rec.transportB CV q ≤ AKLT.Blueprint.Rec.transportRho := by
    dsimp [AKLT.Blueprint.Rec.transportTheta, AKLT.Blueprint.Rec.transportRho]
    nlinarith [hbudget]
  refine ⟨hthetaq, htheta1, hrhotheta, hrho_lt, ?_, hlast⟩
  simpa [b] using hbtheta

end AKLT.W.REC069
