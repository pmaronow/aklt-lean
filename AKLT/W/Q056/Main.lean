module
public import AKLT.Blueprint.Q.NodesEnergy

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Challenge
open AKLT.Blueprint.Q

namespace AKLT.W.Q056

private theorem originalLeg_colours_ne {κ : Plane → Fin 3}
    (hκ : ProperPlaneColouring κ) {W : Finset Plane} {e : Plane × Plane}
    (he : e ∈ originalLegs W) : κ e.1 ≠ κ e.2 := by
  classical
  unfold originalLegs at he
  obtain ⟨x, hx, he⟩ := Finset.mem_biUnion.mp he
  obtain ⟨z, hz, heq⟩ := Finset.mem_image.mp he
  subst e
  have hz' : z ∈ neighbours x := (Finset.mem_sdiff.mp hz).1
  unfold neighbours at hz'
  obtain ⟨d, _, hzd⟩ := Finset.mem_image.mp hz'
  have hadj : Adjacent x z := by
    change latticeDist x z = 1
    rw [← hzd]
    cases d <;> simp [latticeDist, Compass.step]
  exact hκ x z hadj

private theorem normalize_positive_probability {Ω : Type*} [Fintype Ω]
    [Nonempty Ω] (w : Weight Ω) (hw : ∀ a, 0 < w a) :
    PositiveProbability (AKLT.Defs.normalize w) := by
  classical
  have hsum : 0 < ∑ a : Ω, w a :=
    Finset.sum_pos (fun a _ => hw a) Finset.univ_nonempty
  constructor
  · intro a
    exact div_pos (hw a) hsum
  · unfold AKLT.Defs.normalize
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt hsum)

theorem main : AKLT.Blueprint.Q.PlaneProductReferenceStatement := by
  classical
  intro hBounds κ hκ W η
  have hframe : 0 < frameBound := by
    have hs : Real.sqrt (5 : ℝ) * Real.sqrt 5 = 5 := by
      rw [← pow_two, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
    have hn : 0 ≤ Real.sqrt (5 : ℝ) := Real.sqrt_nonneg 5
    have hlt : Real.sqrt (5 : ℝ) < 5 := by nlinarith
    unfold frameBound
    linarith
  have hsite : ∀ x : W, ∀ a : IcoLetter, 0 < planeSiteWeight κ W η x a := by
    intro x a
    unfold planeSiteWeight
    apply mul_pos
    · norm_num
    · apply Finset.prod_pos
      intro e he
      rcases Finset.mem_filter.mp he with ⟨he, hfirst⟩
      have hcol : κ e.1 ≠ κ e.2 := originalLeg_colours_ne hκ he
      have hb := (hBounds (κ e.1) (κ e.2) hcol a
        (extendBoundary η e.2)).1
      have hb' : frameBound ≤
          1 + dot (frameVector (κ x.val) a)
            (frameVector (κ e.2) (extendBoundary η e.2)) := by
        simpa only [hfirst] using hb
      exact lt_of_lt_of_le hframe hb'
  have hlocal : ∀ x : W,
      PositiveProbability (AKLT.Defs.normalize (planeSiteWeight κ W η x)) := by
    intro x
    exact normalize_positive_probability (planeSiteWeight κ W η x) (hsite x)
  refine ⟨hlocal, ?_⟩
  constructor
  · intro σ
    unfold planeProductReference
    apply Finset.prod_pos
    intro x hx
    exact (hlocal x).1 (σ x)
  · unfold planeProductReference
    calc
      (∑ σ : PlaneConfiguration W,
          ∏ x : W, normalize (planeSiteWeight κ W η x) (σ x))
          = ∏ x : W, ∑ a : IcoLetter, normalize (planeSiteWeight κ W η x) a := by
              exact (Fintype.prod_sum (fun x a =>
                normalize (planeSiteWeight κ W η x) a)).symm
      _ = 1 := by
        apply Finset.prod_eq_one
        intro x hx
        exact (hlocal x).2

end AKLT.W.Q056
