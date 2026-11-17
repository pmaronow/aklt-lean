module
public import AKLT.W.REC022.Factorization

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Rec

namespace AKLT.W.REC022

/-- Subtract the two logarithmic partition quotients and collect the three
pair responses. All finite-spin and real-analysis inputs are proved locally. -/
theorem main : AKLT.Blueprint.Rec.ThreeLogIdentityStatement := by
  intro a hU f g hn hof hog hfg
  let It := responseI a.D a.τ true a.y a.o f g
  let I0 := responseI a.D a.τ false a.y a.o f g
  let Jt := responseJ a.D a.τ true a.y f g
  let J0 := responseJ a.D a.τ false a.y f g
  let LI := logarithmicMean It I0
  let LJ := logarithmicMean Jt J0
  have hIt : 0 < It := responseI_pos a.D a.τ true a.y a.o f g
  have hI0 : 0 < I0 := responseI_pos a.D a.τ false a.y a.o f g
  have hJt : 0 < Jt := responseJ_pos a.D a.τ true a.y f g
  have hJ0 : 0 < J0 := responseJ_pos a.D a.τ false a.y f g
  have hlogI := logMean_identity It I0 hIt hI0
  have hlogJ := logMean_identity Jt J0 hJt hJ0
  have hLI : 0 < LI := hlogI.1
  have hLJ : 0 < LJ := hlogJ.1
  have hI : It - I0 =
      (pairResponse a.D a.τ a.y f g + pairResponse a.D a.τ a.y f a.o +
        pairResponse a.D a.τ a.y g a.o) / 3 := by
    dsimp [It,I0,responseI,pairResponse]
    ring
  have hJ : Jt - J0 = pairResponse a.D a.τ a.y f g / 5 := by
    dsimp [Jt,J0,responseJ,pairResponse]
    ring
  rw [step_log_ratio a hU f g hn hof hog hfg false,
    step_log_ratio a hU f g hn hof hog hfg true]
  change Real.log (J0 / I0) - Real.log (Jt / It) = _
  calc
    Real.log (J0 / I0) - Real.log (Jt / It) =
        (Real.log It - Real.log I0) - (Real.log Jt - Real.log J0) := by
      rw [Real.log_div (ne_of_gt hJ0) (ne_of_gt hI0),
        Real.log_div (ne_of_gt hJt) (ne_of_gt hIt)]
      ring
    _ = (It - I0) / LI - (Jt - J0) / LJ := by rw [hlogI.2,hlogJ.2]
    _ = responseAlpha a.D a.τ a.y a.o f g * pairResponse a.D a.τ a.y f g +
        responseBeta a.D a.τ a.y a.o f g *
          (pairResponse a.D a.τ a.y f a.o + pairResponse a.D a.τ a.y g a.o) := by
      rw [hI,hJ]
      dsimp [responseAlpha,responseBeta,LI,LJ]
      field_simp [ne_of_gt hLI,ne_of_gt hLJ]
      ring

end AKLT.W.REC022
