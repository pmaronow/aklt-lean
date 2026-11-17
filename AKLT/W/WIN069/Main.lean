import AKLT.Blueprint.Win.NodesCut

noncomputable section
open scoped BigOperators
open AKLT.Defs
open AKLT.Blueprint.Win

namespace AKLT.W.WIN069

private theorem normalize_scale {Ω : Type*} [Fintype Ω] (a : ℝ) (w : Ω → ℝ)
    (ha : a ≠ 0) : AKLT.Defs.normalize (fun x => a * w x) = AKLT.Defs.normalize w := by
  funext x
  by_cases hsum : ∑ y, w y = 0
  · simp [AKLT.Defs.normalize, hsum, ← Finset.mul_sum]
  · simp only [AKLT.Defs.normalize, ← Finset.mul_sum]
    field_simp [ha, hsum]

private theorem reconstruct_removed_sum (G X : Finset Plane) (τ : PinAssignment G)
    (hPX : 0 < pinnedSum G X τ (fun _ => 1))
    (hP0 : 0 < pinnedSum G ∅ τ (fun _ => 1))
    (hFX : 0 < freeSum G X (fun _ => 1))
    (hF0 : 0 < freeSum G ∅ (fun _ => 1)) :
    pinnedSum G ∅ τ (fun _ => 1) =
      pinnedSum G X τ (fun _ => 1) *
        (freeSum G ∅ (fun _ => 1) / freeSum G X (fun _ => 1)) *
        Real.exp (-AKLT.Blueprint.Win.cutError G X τ) := by
  let PX := pinnedSum G X τ (fun _ => 1)
  let P0 := pinnedSum G ∅ τ (fun _ => 1)
  let FX := freeSum G X (fun _ => 1)
  let F0 := freeSum G ∅ (fun _ => 1)
  have hPX' : 0 < PX := hPX
  have hP0' : 0 < P0 := hP0
  have hFX' : 0 < FX := hFX
  have hF0' : 0 < F0 := hF0
  have hratioX : 0 < PX / FX := div_pos hPX' hFX'
  have hratio0 : 0 < P0 / F0 := div_pos hP0' hF0'
  have he : Real.exp (-AKLT.Blueprint.Win.cutError G X τ) = (P0 / F0) / (PX / FX) := by
    have hcut : AKLT.Blueprint.Win.cutError G X τ = Real.log (PX / FX) - Real.log (P0 / F0) := by
      simp [AKLT.Blueprint.Win.cutError, AKLT.Blueprint.Win.logRatio,
        AKLT.Defs.partitionRatio, PX, P0, FX, F0]
    rw [hcut, show -(Real.log (PX / FX) - Real.log (P0 / F0)) =
      Real.log (P0 / F0) - Real.log (PX / FX) by ring, Real.exp_sub,
      Real.exp_log hratio0, Real.exp_log hratioX]
  calc
    P0 = PX * (F0 / FX) * ((P0 / F0) / (PX / FX)) := by
      field_simp
    _ = PX * (F0 / FX) * Real.exp (-AKLT.Blueprint.Win.cutError G X τ) := by rw [← he]

theorem main : AKLT.Blueprint.Win.WindowRewriteStatement := by
  classical
  intro κ F B X G₁ G₂ hcut unit hpositive hweight hmarg hfactor hinvariant
  let η₀ : FrameBoundary F := fun _ => (0, 0, 0)
  let s₀ : PlaneConfiguration B := fun _ => (0, 0, 0)
  let G := F \ B
  let w : Weight (PlaneConfiguration B) := fun s =>
    windowWeight κ B s * componentSum G G₁ (cutPins κ G F B unit η₀ s)
  have hcomp₁ : ∀ s : PlaneConfiguration B,
      0 < componentSum G G₁ (cutPins κ G F B unit η₀ s) := by
    intro s
    exact hpositive G (G \ G₁) (cutPins κ G F B unit η₀ s) |>.1
  have hcomp₂ : ∀ η : FrameBoundary F,
      0 < componentSum G G₂ (cutPins κ G F B unit η s₀) := by
    intro η
    exact hpositive G (G \ G₂) (cutPins κ G F B unit η s₀) |>.1
  have hw : ∀ s, 0 < w s := by
    intro s
    dsimp [w]
    exact mul_pos (hweight s) (hcomp₁ s)
  refine ⟨w, hw, ?_⟩
  intro η
  have hscale : 0 < freeSum G ∅ (fun _ => 1) / freeSum G X (fun _ => 1) :=
    div_pos (hpositive G ∅ (cutPins κ G F B unit η s₀) |>.2)
      (hpositive G X (cutPins κ G F B unit η s₀) |>.2)
  let c : ℝ :=
    (freeSum G ∅ (fun _ => 1) / freeSum G X (fun _ => 1)) *
      componentSum G G₂ (cutPins κ G F B unit η s₀)
  have hc : 0 < c := mul_pos hscale (hcomp₂ η)
  have hpoint : ∀ s : PlaneConfiguration B,
      windowWeight κ B s *
          pinnedSum G ∅ (cutPins κ G F B unit η s) (fun _ => 1) =
        c * (w s * Real.exp (-AKLT.Blueprint.Win.cutError G X
          (cutPins κ G F B unit η s))) := by
    intro s
    let τ := cutPins κ G F B unit η s
    have hPX := hpositive G X τ
    have hP0 := hpositive G ∅ τ
    have hFX := hpositive G X τ
    have hF0 := hpositive G ∅ τ
    have hfactor' : pinnedSum G X τ (fun _ => 1) =
        componentSum G G₁ τ * componentSum G G₂ τ := hfactor τ
    have hinv := hinvariant η η₀ s s₀
    have hcomp1' : componentSum G G₁ τ =
        componentSum G G₁ (cutPins κ G F B unit η₀ s) := hinv.1
    have hcomp2' : componentSum G G₂ τ =
        componentSum G G₂ (cutPins κ G F B unit η s₀) := hinv.2
    have hreconstruct := reconstruct_removed_sum G X τ hPX.1 hP0.1 hFX.2 hF0.2
    rw [hreconstruct, hfactor', hcomp1', hcomp2']
    dsimp [c, w]
    ring
  have hfun : (fun s : PlaneConfiguration B =>
      windowWeight κ B s * pinnedSum G ∅ (cutPins κ G F B unit η s) (fun _ => 1)) =
      (fun s => c * (w s * Real.exp (-AKLT.Blueprint.Win.cutError G X
        (cutPins κ G F B unit η s)))) := by
    funext s
    exact hpoint s
  rw [hmarg η]
  rw [hfun]
  rw [normalize_scale c _ hc.ne']

#print axioms main

end AKLT.W.WIN069
