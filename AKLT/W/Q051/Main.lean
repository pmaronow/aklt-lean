module
public import AKLT.Blueprint.Q.NodesEnergy

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Challenge

namespace AKLT.W.Q051

local instance (α : Type) : DecidableEq α := Classical.decEq α
attribute [local instance] Classical.propDecidable

private def edgeFactor {L N : Size} (κ : Site L N → Fin 3)
    (τ : TorusConfiguration L N) (e : Bond L N) : ℝ :=
  1 - dot (frameVector (κ e.1) (τ e.1))
    (frameVector (κ (nextSite e.1 e.2)) (τ (nextSite e.1 e.2)))

private def swapConfig {L N : Size} (U : Finset (Site L N))
    (σ ξ τ : TorusConfiguration L N) : TorusConfiguration L N :=
  fun x => if x ∈ U then τ x else Equiv.swap (σ x) (ξ x) (τ x)

private def swapConfigEquiv {L N : Size} (U : Finset (Site L N))
    (σ ξ : TorusConfiguration L N) :
    TorusConfiguration L N ≃ TorusConfiguration L N where
  toFun := swapConfig U σ ξ
  invFun := swapConfig U σ ξ
  left_inv := by
    intro τ
    funext x
    by_cases hx : x ∈ U
    · simp [swapConfig, hx]
    · simp [swapConfig, hx]
  right_inv := by
    intro τ
    funext x
    by_cases hx : x ∈ U
    · simp [swapConfig, hx]
    · simp [swapConfig, hx]

private theorem frameBound_pos : 0 < frameBound := by
  dsimp [frameBound]
  have hs : Real.sqrt 5 < 5 := by nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
  positivity

private theorem edgeFactor_pos {L N : Size} (hBounds : AKLT.Blueprint.Q.interactionBounds)
    (κ : Site L N → Fin 3) (hκ : ProperTorusColoring κ)
    (τ : TorusConfiguration L N) (e : Bond L N) : 0 < edgeFactor κ τ e := by
  have hdiff : κ e.1 ≠ κ (nextSite e.1 e.2) := hκ e
  exact lt_of_lt_of_le frameBound_pos (hBounds _ _ hdiff _ _).2.2.1

private theorem swapConfig_fiber {L N : Size} (U : Finset (Site L N))
    (σ ξ τ : TorusConfiguration L N)
    (hτ : AgreeOutside U σ τ) :
    AgreeOutside U ξ (swapConfig U σ ξ τ) := by
  intro x hx
  simp [swapConfig, hx, hτ x hx, Equiv.swap_apply_left]

private theorem swapConfig_fiber_iff {L N : Size} (U : Finset (Site L N))
    (σ ξ τ : TorusConfiguration L N) :
    AgreeOutside U σ τ ↔ AgreeOutside U ξ (swapConfig U σ ξ τ) := by
  constructor
  · exact swapConfig_fiber U σ ξ τ
  · intro h x hx
    have h' := congrArg (Equiv.swap (σ x) (ξ x)) (h x hx)
    simpa [swapConfig, hx, Equiv.swap_apply_left, Equiv.swap_apply_self] using h'

private theorem swapConfig_inside {L N : Size} (U : Finset (Site L N))
    (σ ξ τ : TorusConfiguration L N) (x : U) :
    swapConfig U σ ξ τ x.val = τ x.val := by
  simp [swapConfig, x.property]

private theorem boundary_neighbor_of_crossing {L N : Size}
    (U : Finset (Site L N)) (e : Bond L N)
    (hTouch : e.1 ∈ U ∨ nextSite e.1 e.2 ∈ U)
    (hOne : ¬ (e.1 ∈ U ∧ nextSite e.1 e.2 ∈ U)) :
    (if e.1 ∈ U then nextSite e.1 e.2 else e.1) ∈
      U.biUnion torusNeighbors \ U := by
  classical
  rcases hTouch with hs | ht
  · have hout : nextSite e.1 e.2 ∉ U := by
      intro h
      exact hOne ⟨hs, h⟩
    have hn : nextSite e.1 e.2 ∈ torusNeighbors e.1 := by
      have hd : e.2.val = 0 ∨ e.2.val = 1 := by omega
      rcases hd with hd | hd
      · have hdir : e.2 = 0 := Fin.ext hd
        rw [hdir]
        simp [nextSite, torusNeighbors]
      · have hdir : e.2 = 1 := Fin.ext hd
        rw [hdir]
        simp [nextSite, torusNeighbors]
    rw [if_pos hs]
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_biUnion.mpr ⟨e.1, hs, hn⟩, hout⟩
  · have hout : e.1 ∉ U := by
      intro h
      exact hOne ⟨h, ht⟩
    have hn : e.1 ∈ torusNeighbors (nextSite e.1 e.2) := by
      have hd : e.2.val = 0 ∨ e.2.val = 1 := by omega
      rcases hd with hd | hd
      · have hdir : e.2 = 0 := Fin.ext hd
        rw [hdir]
        simp [nextSite, torusNeighbors]
      · have hdir : e.2 = 1 := Fin.ext hd
        rw [hdir]
        simp [nextSite, torusNeighbors]
    rw [if_neg hout]
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_biUnion.mpr ⟨nextSite e.1 e.2, ht, hn⟩, hout⟩

private theorem marginal_conditionOn_ratio {Ω Ξ : Type} [Fintype Ω] [Fintype Ξ]
    [DecidableEq Ξ] (p : Weight Ω) (E : Ω → Prop) (r : Ω → Ξ) (a : Ξ) :
    marginal (conditionOn p E) r a =
      (∑ x, if E x ∧ r x = a then p x else 0) /
        (∑ x, if E x then p x else 0) := by
  classical
  let cut : Ω → ℝ := fun x => if E x then p x else 0
  let Z := ∑ x, cut x
  change (∑ x, if r x = a then cut x / Z else 0) =
    (∑ x, if E x ∧ r x = a then p x else 0) / (∑ x, if E x then p x else 0)
  have hsum : (∑ x, if r x = a then cut x / Z else 0) =
      (∑ x, if E x ∧ r x = a then p x else 0) / Z := by
    calc
      (∑ x, if r x = a then cut x / Z else 0) =
          ∑ x, (if E x ∧ r x = a then p x else 0) / Z := by
        apply Finset.sum_congr rfl
        intro x hx
        by_cases he : E x <;> by_cases hr : r x = a <;> simp [cut, he, hr]
      _ = (∑ x, if E x ∧ r x = a then p x else 0) / Z := by
        rw [← Finset.sum_div]
  rw [hsum]

private def edgeTouches {L N : Size} (U : Finset (Site L N)) (e : Bond L N) : Prop :=
  e.1 ∈ U ∨ nextSite e.1 e.2 ∈ U

private def edgeScale {L N : Size} (κ : Site L N → Fin 3) (U : Finset (Site L N))
    (σ ξ : TorusConfiguration L N) (e : Bond L N) : ℝ :=
  if edgeTouches U e then 1 else edgeFactor κ ξ e / edgeFactor κ σ e

private def exteriorScale {L N : Size} (κ : Site L N → Fin 3) (U : Finset (Site L N))
    (σ ξ : TorusConfiguration L N) : ℝ :=
  ∏ e : Bond L N, edgeScale κ U σ ξ e

private theorem swapConfig_eq_fixed {L N : Size} (U : Finset (Site L N))
    (σ ξ τ : TorusConfiguration L N) (hτ : AgreeOutside U σ τ)
    (hBoundary : ∀ z ∈ U.biUnion torusNeighbors \ U, σ z = ξ z)
    {x : Site L N} (hx : x ∈ U ∨ x ∈ U.biUnion torusNeighbors \ U) :
    swapConfig U σ ξ τ x = τ x := by
  rcases hx with hx | hx
  · simp [swapConfig, hx]
  · have hxout : x ∉ U := (Finset.mem_sdiff.mp hx).2
    have hsx := hBoundary x hx
    have htx := hτ x hxout
    simp [swapConfig, hxout, hsx, htx]

private theorem touchedEndpoints_fixed {L N : Size} (U : Finset (Site L N))
    (e : Bond L N) (ht : edgeTouches U e) :
    (e.1 ∈ U ∨ e.1 ∈ U.biUnion torusNeighbors \ U) ∧
      (nextSite e.1 e.2 ∈ U ∨ nextSite e.1 e.2 ∈ U.biUnion torusNeighbors \ U) := by
  rcases ht with hs | hd
  · constructor
    · exact Or.inl hs
    · by_cases hdt : nextSite e.1 e.2 ∈ U
      · exact Or.inl hdt
      · refine Or.inr ?_
        have hb := boundary_neighbor_of_crossing U e (Or.inl hs) (by
          intro h
          exact hdt h.2)
        simpa [hs] using hb
  · constructor
    · by_cases hs : e.1 ∈ U
      · exact Or.inl hs
      · refine Or.inr ?_
        have hb := boundary_neighbor_of_crossing U e (Or.inr hd) (by
          intro h
          exact hs h.1)
        simpa [hs] using hb
    · exact Or.inl hd

private theorem edgeFactor_swap_touched {L N : Size}
    (hBounds : AKLT.Blueprint.Q.interactionBounds)
    (κ : Site L N → Fin 3) (hκ : ProperTorusColoring κ)
    (U : Finset (Site L N)) (σ ξ τ : TorusConfiguration L N)
    (hτ : AgreeOutside U σ τ)
    (hBoundary : ∀ z ∈ U.biUnion torusNeighbors \ U, σ z = ξ z)
    (e : Bond L N) (ht : edgeTouches U e) :
    edgeFactor κ (swapConfig U σ ξ τ) e = edgeFactor κ τ e := by
  have hend := touchedEndpoints_fixed U e ht
  have h₁ := swapConfig_eq_fixed U σ ξ τ hτ hBoundary hend.1
  have h₂ := swapConfig_eq_fixed U σ ξ τ hτ hBoundary hend.2
  simp [edgeFactor, h₁, h₂]

private theorem edgeFactor_swap_untouched {L N : Size}
    (κ : Site L N → Fin 3) (U : Finset (Site L N))
    (σ ξ τ : TorusConfiguration L N) (hτ : AgreeOutside U σ τ)
    (e : Bond L N) (ht : ¬ edgeTouches U e) :
    edgeFactor κ (swapConfig U σ ξ τ) e = edgeFactor κ ξ e := by
  have hs : e.1 ∉ U := fun h => ht (Or.inl h)
  have hd : nextSite e.1 e.2 ∉ U := fun h => ht (Or.inr h)
  have h₁ : swapConfig U σ ξ τ e.1 = ξ e.1 := by
    simp [swapConfig, hs, hτ e.1 hs, Equiv.swap_apply_left]
  have h₂ : swapConfig U σ ξ τ (nextSite e.1 e.2) = ξ (nextSite e.1 e.2) := by
    simp [swapConfig, hd, hτ (nextSite e.1 e.2) hd, Equiv.swap_apply_left]
  simp [edgeFactor, h₁, h₂]

private theorem edgeFactor_swap_scale {L N : Size}
    (hBounds : AKLT.Blueprint.Q.interactionBounds)
    (κ : Site L N → Fin 3) (hκ : ProperTorusColoring κ)
    (U : Finset (Site L N)) (σ ξ τ : TorusConfiguration L N)
    (hτ : AgreeOutside U σ τ)
    (hBoundary : ∀ z ∈ U.biUnion torusNeighbors \ U, σ z = ξ z)
    (e : Bond L N) :
    edgeFactor κ (swapConfig U σ ξ τ) e = edgeScale κ U σ ξ e * edgeFactor κ τ e := by
  by_cases ht : edgeTouches U e
  · rw [edgeScale, if_pos ht]
    rw [edgeFactor_swap_touched hBounds κ hκ U σ ξ τ hτ hBoundary e ht]
    simp
  · rw [edgeScale, if_neg ht]
    rw [edgeFactor_swap_untouched κ U σ ξ τ hτ e ht]
    have hτσ : edgeFactor κ τ e = edgeFactor κ σ e := by
      have hs := hτ e.1 (fun h => ht (Or.inl h))
      have hd := hτ (nextSite e.1 e.2) (fun h => ht (Or.inr h))
      simp [edgeFactor, hs, hd]
    rw [hτσ]
    have hpos := edgeFactor_pos hBounds κ hκ σ e
    field_simp [ne_of_gt hpos]

private theorem edgeScale_pos {L N : Size}
    (hBounds : AKLT.Blueprint.Q.interactionBounds)
    (κ : Site L N → Fin 3) (hκ : ProperTorusColoring κ)
    (U : Finset (Site L N)) (σ ξ : TorusConfiguration L N)
    (e : Bond L N) : 0 < edgeScale κ U σ ξ e := by
  by_cases ht : edgeTouches U e
  · simp [edgeScale, ht]
  · simp only [edgeScale, ht, ↓reduceIte]
    exact div_pos (edgeFactor_pos hBounds κ hκ ξ e) (edgeFactor_pos hBounds κ hκ σ e)

private theorem exteriorScale_pos {L N : Size}
    (hBounds : AKLT.Blueprint.Q.interactionBounds)
    (κ : Site L N → Fin 3) (hκ : ProperTorusColoring κ)
    (U : Finset (Site L N)) (σ ξ : TorusConfiguration L N) :
    0 < exteriorScale κ U σ ξ := by
  unfold exteriorScale
  exact Finset.prod_pos fun e he => edgeScale_pos hBounds κ hκ U σ ξ e

private theorem torusWeight_swap_scale {L N : Size}
    (hBounds : AKLT.Blueprint.Q.interactionBounds)
    (κ : Site L N → Fin 3) (hκ : ProperTorusColoring κ)
    (U : Finset (Site L N)) (σ ξ τ : TorusConfiguration L N)
    (hτ : AgreeOutside U σ τ)
    (hBoundary : ∀ z ∈ U.biUnion torusNeighbors \ U, σ z = ξ z) :
    torusWeight L N κ (swapConfig U σ ξ τ) =
      exteriorScale κ U σ ξ * torusWeight L N κ τ := by
  have hp : ∀ e : Bond L N,
      edgeFactor κ (swapConfig U σ ξ τ) e = edgeScale κ U σ ξ e * edgeFactor κ τ e :=
    fun e => edgeFactor_swap_scale hBounds κ hκ U σ ξ τ hτ hBoundary e
  have hprod : (∏ e : Bond L N, edgeFactor κ (swapConfig U σ ξ τ) e) =
      (∏ e : Bond L N, edgeScale κ U σ ξ e) *
        (∏ e : Bond L N, edgeFactor κ τ e) := by
    calc
      (∏ e : Bond L N, edgeFactor κ (swapConfig U σ ξ τ) e) =
          ∏ e : Bond L N, edgeScale κ U σ ξ e * edgeFactor κ τ e := by
            apply Finset.prod_congr rfl
            intro e he
            exact hp e
      _ = _ := Finset.prod_mul_distrib
  change (∏ _x : Site L N, (1 / 12 : ℝ)) *
      (∏ e : Bond L N, edgeFactor κ (swapConfig U σ ξ τ) e) =
    exteriorScale κ U σ ξ *
      ((∏ _x : Site L N, (1 / 12 : ℝ)) * (∏ e : Bond L N, edgeFactor κ τ e))
  rw [exteriorScale, hprod]
  ring

private theorem sum_if_normalize {Ω : Type} [Fintype Ω] (w : Weight Ω)
    (E : Ω → Prop) [DecidablePred E] :
    (∑ x, if E x then normalize w x else 0) =
      (∑ x, if E x then w x else 0) / (∑ x, w x) := by
  classical
  change (∑ x, if E x then w x / (∑ y, w y) else 0) = _
  calc
    (∑ x, if E x then w x / (∑ y, w y) else 0) =
        ∑ x, (if E x then w x else 0) / (∑ y, w y) := by
      apply Finset.sum_congr rfl
      intro x hx
      by_cases he : E x <;> simp [he]
    _ = _ := by rw [← Finset.sum_div]

private theorem ratio_normalize {Ω : Type} [Fintype Ω] (w : Weight Ω)
    (P E : Ω → Prop) [DecidablePred P] [DecidablePred E]
    (hZ : (∑ x, w x) ≠ 0) :
    (∑ x, if P x then normalize w x else 0) /
        (∑ x, if E x then normalize w x else 0) =
      (∑ x, if P x then w x else 0) /
        (∑ x, if E x then w x else 0) := by
  rw [sum_if_normalize, sum_if_normalize]
  field_simp [hZ]

private theorem torusWeight_pos {L N : Size}
    (hBounds : AKLT.Blueprint.Q.interactionBounds)
    (κ : Site L N → Fin 3) (hκ : ProperTorusColoring κ)
    (τ : TorusConfiguration L N) : 0 < torusWeight L N κ τ := by
  unfold torusWeight
  apply mul_pos
  · exact Finset.prod_pos fun _ _ => by norm_num
  · exact Finset.prod_pos fun e _ => edgeFactor_pos hBounds κ hκ τ e

private theorem torusPartition_pos {L N : Size}
    (hBounds : AKLT.Blueprint.Q.interactionBounds)
    (κ : Site L N → Fin 3) (hκ : ProperTorusColoring κ) :
    0 < ∑ τ : TorusConfiguration L N, torusWeight L N κ τ := by
  classical
  have hne : (Finset.univ : Finset (TorusConfiguration L N)).Nonempty :=
    ⟨fun _ => default, Finset.mem_univ _⟩
  exact Finset.sum_pos (fun τ _ => torusWeight_pos hBounds κ hκ τ) hne

private def fiberSum {L N : Size} (κ : Site L N → Fin 3)
    (U : Finset (Site L N)) (σ : TorusConfiguration L N)
    (P : TorusConfiguration L N → Prop) (dP : DecidablePred P) : ℝ := by
  classical
  letI : DecidablePred P := dP
  exact ∑ τ, if AgreeOutside U σ τ ∧ P τ then torusWeight L N κ τ else 0

private theorem fiberSum_swap_scale {L N : Size}
    (hBounds : AKLT.Blueprint.Q.interactionBounds)
    (κ : Site L N → Fin 3) (hκ : ProperTorusColoring κ)
    (U : Finset (Site L N)) (σ ξ : TorusConfiguration L N)
    (hBoundary : ∀ z ∈ U.biUnion torusNeighbors \ U, σ z = ξ z)
    (P : TorusConfiguration L N → Prop)
    (dP : DecidablePred P)
    (hP : ∀ τ, P (swapConfig U σ ξ τ) ↔ P τ) :
    fiberSum κ U ξ P dP = exteriorScale κ U σ ξ * fiberSum κ U σ P dP := by
  classical
  let e := swapConfigEquiv U σ ξ
  calc
    fiberSum κ U ξ P dP =
        ∑ τ, if AgreeOutside U ξ (e τ) ∧ P (e τ) then
            torusWeight L N κ (e τ) else 0 := by
      unfold fiberSum
      exact (Equiv.sum_comp e
        (fun τ => if AgreeOutside U ξ τ ∧ P τ then torusWeight L N κ τ else 0)).symm
    _ = ∑ τ, exteriorScale κ U σ ξ *
          (if AgreeOutside U σ τ ∧ P τ then torusWeight L N κ τ else 0) := by
      apply Finset.sum_congr rfl
      intro τ hτ'
      have hf : AgreeOutside U ξ (e τ) ↔ AgreeOutside U σ τ := by
        simpa [e, swapConfigEquiv] using (swapConfig_fiber_iff U σ ξ τ).symm
      have hq : P (e τ) ↔ P τ := by
        simpa [e, swapConfigEquiv] using hP τ
      by_cases hp : AgreeOutside U σ τ ∧ P τ
      · have hp' : AgreeOutside U ξ (e τ) ∧ P (e τ) := ⟨hf.mpr hp.1, hq.mpr hp.2⟩
        have hw := torusWeight_swap_scale hBounds κ hκ U σ ξ τ hp.1 hBoundary
        rw [if_pos hp', if_pos hp]
        simpa [e, swapConfigEquiv] using hw
      · have hp' : ¬ (AgreeOutside U ξ (e τ) ∧ P (e τ)) := by
          intro hh
          exact hp ⟨hf.mp hh.1, hq.mp hh.2⟩
        simp [hp, hp']
    _ = exteriorScale κ U σ ξ * fiberSum κ U σ P dP := by
      rw [← Finset.mul_sum]
      rfl

private theorem conditionalTorusLaw_fiberSum {L N : Size}
    (hBounds : AKLT.Blueprint.Q.interactionBounds)
    (κ : Site L N → Fin 3) (hκ : ProperTorusColoring κ)
    (U : Finset (Site L N)) (σ : TorusConfiguration L N)
    (ζ : U → IcoLetter) :
    conditionalTorusLaw L N κ U σ ζ =
      fiberSum κ U σ (fun τ => (fun x : U => τ x.val) = ζ)
        (fun τ => Fintype.decidablePiFintype (fun x : U => τ x.val) ζ) /
        fiberSum κ U σ (fun _ => True) (fun _ => isTrue trivial) := by
  classical
  letI : DecidablePred (fun τ : TorusConfiguration L N =>
      (fun x : U => τ x.val) = ζ) :=
    fun τ => Fintype.decidablePiFintype (fun x : U => τ x.val) ζ
  letI : DecidablePred (fun τ : TorusConfiguration L N => AgreeOutside U σ τ) :=
    fun τ => Classical.propDecidable _
  unfold conditionalTorusLaw
  rw [marginal_conditionOn_ratio]
  change (∑ τ, if AgreeOutside U σ τ ∧ (fun x : U => τ x.val) = ζ then
      torusLaw L N κ τ else 0) /
      (∑ τ, if AgreeOutside U σ τ then torusLaw L N κ τ else 0) = _
  have hZ : (∑ τ : TorusConfiguration L N, torusWeight L N κ τ) ≠ 0 :=
    (torusPartition_pos hBounds κ hκ).ne'
  simp only [torusLaw]
  simpa [fiberSum] using ratio_normalize (torusWeight L N κ)
    (fun τ => AgreeOutside U σ τ ∧ (fun x : U => τ x.val) = ζ)
    (fun τ => AgreeOutside U σ τ) hZ

theorem main : AKLT.Blueprint.Q.TorusMarkovStatement := by
  intro hBounds L N κ hκ U σ ξ hBoundary
  classical
  funext ζ
  let dζ : DecidablePred (fun τ : TorusConfiguration L N =>
      (fun x : U => τ x.val) = ζ) :=
    fun τ => Fintype.decidablePiFintype (fun x : U => τ x.val) ζ
  rw [conditionalTorusLaw_fiberSum hBounds κ hκ U σ ζ,
    conditionalTorusLaw_fiberSum hBounds κ hκ U ξ ζ]
  have hP : ∀ τ, (fun x : U => swapConfig U σ ξ τ x.val) = ζ ↔
      (fun x : U => τ x.val) = ζ := by
    intro τ
    have hinside : (fun x : U => swapConfig U σ ξ τ x.val) =
        (fun x : U => τ x.val) := by
      funext x
      exact swapConfig_inside U σ ξ τ x
    rw [hinside]
  have hNum := fiberSum_swap_scale hBounds κ hκ U σ ξ hBoundary
    (fun τ => (fun x : U => τ x.val) = ζ) dζ hP
  have hMass := fiberSum_swap_scale hBounds κ hκ U σ ξ hBoundary
    (fun _ => True) (fun _ => isTrue trivial) (by intro τ; simp)
  have hc : exteriorScale κ U σ ξ ≠ 0 :=
    ne_of_gt (exteriorScale_pos hBounds κ hκ U σ ξ)
  change fiberSum κ U σ (fun τ => (fun x : U => τ x.val) = ζ) dζ /
      fiberSum κ U σ (fun _ => True) (fun _ => isTrue trivial) =
    fiberSum κ U ξ (fun τ => (fun x : U => τ x.val) = ζ) dζ /
      fiberSum κ U ξ (fun _ => True) (fun _ => isTrue trivial)
  rw [hNum, hMass]
  field_simp [hc]

end AKLT.W.Q051
