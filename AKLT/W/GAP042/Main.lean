module
public import AKLT.Blueprint.Gap.NodesPeriodic

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
set_option maxHeartbeats 800000

namespace AKLT.W.GAP042

open AKLT.Defs AKLT.Blueprint.Gap
attribute [local instance] Classical.propDecidable

private theorem window_subset_farVolume (a y : Plane) (u l : ℕ) (i : ℤ)
    (hu : 1 ≤ u) : window a y u l i ⊆ farVolume a y u i := by
  classical
  intro x hx
  have hxShell : x ∈ shell a y u i :=
    (Finset.mem_sdiff.mp (by simpa [window] using hx)).1
  have hxData : x ∈ square a u ∧ (supDist x y : ℤ) = shellRadius u i := by
    simpa [shell] using hxShell
  rcases hxData with ⟨hxSquare, hxRadius⟩
  have huR : (1 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu
  have hs : (1 : ℝ) ≤ shellSpacing u := by
    unfold shellSpacing
    exact Real.one_le_sqrt.mpr (Real.one_le_sqrt.mpr huR)
  have hfloor : ((i : ℝ) * shellSpacing u - 1) < (shellRadius u i : ℝ) := by
    simp [shellRadius, Int.sub_one_lt_floor]
  have hxRadiusR : (supDist x y : ℝ) = (shellRadius u i : ℝ) := by
    exact_mod_cast hxRadius
  have hdist : ((i : ℝ) - 1) * shellSpacing u < (supDist x y : ℝ) := by
    rw [hxRadiusR]
    calc
      ((i : ℝ) - 1) * shellSpacing u ≤ (i : ℝ) * shellSpacing u - 1 := by
        nlinarith
      _ < (shellRadius u i : ℝ) := hfloor
  change x ∈ (square a u).filter
    (fun z => ((i : ℝ) - 1) * shellSpacing u < supDist z y)
  exact Finset.mem_filter.mpr ⟨hxSquare, hdist⟩

private theorem frameMarginal_eq (κ : Plane → Fin 3) (W V : Finset Plane)
    (hVW : V ⊆ W) (η : Plane → IcoLetter) :
    specMarginal (frameSpec κ) W V η =
      planeMarginal κ W V (fun z : exteriorSites W => η z.val) := by
  classical
  let ηP : Config (frameSpec κ).Letter := fun z => η z
  unfold specMarginal planeMarginal frameSpec
  change marginal (planeLaw κ W (fun z : exteriorSites W => η z.val))
      (fun (σ : PlaneConfiguration W) => restrict V (fill (frameSpec κ) W ηP σ)) =
    marginal (planeLaw κ W (fun z : exteriorSites W => η z.val))
      (fun (σ : PlaneConfiguration W) (x : V) => extendLetters σ x.val)
  ext t
  simp only [marginal]
  apply Finset.sum_congr rfl
  intro σ hσ
  have hmaps : restrict V (fill (frameSpec κ) W ηP σ) =
      (fun x : V => extendLetters σ x.val) := by
    funext x
    simp [restrict, fill, extendLetters, hVW x.property]
    apply congrArg σ
    exact Subtype.ext rfl
  have hcond :
      (restrict V (fill (frameSpec κ) W ηP σ) = t) ↔
        (fun x : V => extendLetters σ x.val) = t := by
    rw [hmaps]
    rfl
  by_cases h : (fun x : V => extendLetters σ x.val) = t
  · have hleft := hcond.mpr h
    rw [ite_eq_left hleft, ite_eq_left h]
  · have hleft : ¬ restrict V (fill (frameSpec κ) W ηP σ) = t :=
      fun h' => h (hcond.mp h')
    rw [ite_eq_right hleft, ite_eq_right h]

theorem main : AKLT.Blueprint.Gap.FrameWindowTransferStatement := by
  classical
  intro l p Mstar hWindow κ hκ
  rcases hWindow with ⟨hl, hMstar, hp, hpone, hW⟩
  refine ⟨hl, hMstar, hp, hpone, ?_⟩
  intro a u hu y hy i hi hishell hiex η ξ
  have hu1 : 1 ≤ u := le_trans hMstar hu
  have hsubset : window a y u l i ⊆ farVolume a y u i :=
    window_subset_farVolume a y u l i hu1
  let ηB : FrameBoundary (farVolume a y u i) := fun z => η z.val
  let ξB : FrameBoundary (farVolume a y u i) := fun z => ξ z.val
  have hη := frameMarginal_eq κ (farVolume a y u i) (window a y u l i) hsubset η
  have hξ := frameMarginal_eq κ (farVolume a y u i) (window a y u l i) hsubset ξ
  rw [hη, hξ]
  exact hW κ hκ a u hu y hy i hi hishell hiex ηB ξB

end AKLT.W.GAP042

end

#print axioms AKLT.W.GAP042.main
