module
public import AKLT.W.WIN063.Edges

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Win

namespace AKLT.W.WIN063

def glueConfig {F B : Finset Plane}
    (s : PlaneConfiguration B) (n : PlaneConfiguration (F \ B)) : PlaneConfiguration F := by
  classical
  exact fun x => if hx : x.val ∈ B then s ⟨x.val, hx⟩ else n ⟨x.val, Finset.mem_sdiff.mpr ⟨x.property, hx⟩⟩

def splitConfig {F B : Finset Plane} (hBF : B ⊆ F)
    (σ : PlaneConfiguration F) : PlaneConfiguration B × PlaneConfiguration (F \ B) := by
  classical
  exact (fun x => σ ⟨x.val, hBF x.property⟩,
    fun x => σ ⟨x.val, (Finset.mem_sdiff.mp x.property).1⟩)

def configEquiv {F B : Finset Plane} (hBF : B ⊆ F) :
    PlaneConfiguration F ≃ PlaneConfiguration B × PlaneConfiguration (F \ B) where
  toFun := splitConfig hBF
  invFun p := glueConfig p.1 p.2
  left_inv := by
    intro σ
    funext x
    dsimp [glueConfig, splitConfig]
    by_cases hx : x.val ∈ B
    · simp [hx]
    · simp [hx]
  right_inv := by
    rintro ⟨s, n⟩
    apply Prod.ext
    · funext x
      simp [glueConfig, splitConfig]
    · funext x
      have hx := x.property
      rw [Finset.mem_sdiff] at hx
      simp [glueConfig, splitConfig, hx.2]


lemma marginalNumerator_eq_sum_glue {κ : Plane → Fin 3} {F B : Finset Plane}
    (hBF : B ⊆ F) (η : FrameBoundary F) (s : PlaneConfiguration B) :
    marginalNumerator κ F B η s =
      ∑ n : PlaneConfiguration (F \ B), planeWeight κ F η (glueConfig s n) := by
  classical
  unfold marginalNumerator
  calc
    (∑ σ : PlaneConfiguration F,
        if (fun z : B => extendLetters σ z.val) = s then planeWeight κ F η σ else 0) =
      ∑ σ : PlaneConfiguration F,
        if (splitConfig hBF σ).1 = s then planeWeight κ F η σ else 0 := by
          apply Finset.sum_congr rfl
          intro σ hσ
          congr 1
          apply propext
          constructor
          · intro hs
            apply funext
            intro z
            have hz : z.val ∈ F := hBF z.property
            simpa [splitConfig, extendLetters, hz] using congrFun hs z
          · intro hs
            apply funext
            intro z
            have hz : z.val ∈ F := hBF z.property
            simpa [splitConfig, extendLetters, hz] using congrFun hs z
    _ = ∑ p : PlaneConfiguration B × PlaneConfiguration (F \ B),
        if p.1 = s then planeWeight κ F η (glueConfig p.1 p.2) else 0 := by
          apply Fintype.sum_equiv (configEquiv hBF)
          intro σ
          have hσ : glueConfig (splitConfig hBF σ).1 (splitConfig hBF σ).2 = σ := by
            simpa [configEquiv] using (configEquiv hBF).left_inv σ
          simp [configEquiv, hσ]
    _ = ∑ n : PlaneConfiguration (F \ B), planeWeight κ F η (glueConfig s n) := by
          rw [Fintype.sum_prod_type_right]
          simp


def sdiffEmptySubtypeEquiv (G : Finset Plane) : (↥(G \ ∅)) ≃ ↥G where
  toFun x := ⟨x.1, (Finset.mem_sdiff.mp x.2).1⟩
  invFun x := ⟨x.1, Finset.mem_sdiff.mpr ⟨x.2, by simp⟩⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv x := by apply Subtype.ext; rfl

def configSdiffEmptyEquiv (G : Finset Plane) :
    PlaneConfiguration (G \ ∅) ≃ PlaneConfiguration G :=
  Equiv.piCongrLeft (fun _ : ↥G => IcoLetter) (sdiffEmptySubtypeEquiv G)


def complementaryFrameTerm (κ : Plane → Fin 3) (G : Finset Plane)
    (τ : PinAssignment G) (n : PlaneConfiguration G) : ℝ :=
  (1 / 12 : ℝ) ^ G.card *
    (∏ e ∈ internalBonds G,
      (1 + dot (frameSpins κ n e.1) (frameSpins κ n e.2))) *
    ∏ e : originalLegs G,
      if e.val.1 ∈ G then 1 + dot (τ e).val (frameSpins κ n e.val.1) else 1

lemma configSdiffEmptyEquiv_same (G : Finset Plane)
    (n : PlaneConfiguration (G \ ∅)) (z : G) :
    (configSdiffEmptyEquiv G n) z = n ⟨z.1, by simp⟩ := by
  change (Equiv.piCongrLeft (fun _ : ↥G => IcoLetter)
    (sdiffEmptySubtypeEquiv G) n) z = n ⟨z.1, by simp⟩
  rw [Equiv.piCongrLeft_apply]
  simp [sdiffEmptySubtypeEquiv]

lemma frameSpins_sdiffEmpty (κ : Plane → Fin 3) (G : Finset Plane)
    (n : PlaneConfiguration (G \ ∅)) (z : Plane) :
    frameSpins κ n z = frameSpins κ (configSdiffEmptyEquiv G n) z := by
  by_cases hz : z ∈ G
  · simp [frameSpins, hz, configSdiffEmptyEquiv_same]
  · simp [frameSpins, hz]


lemma framePinnedSum_eq_complementaryFrameTerm (κ : Plane → Fin 3) (G : Finset Plane)
    (τ : PinAssignment G) :
    framePinnedSum κ G ∅ τ = ∑ n : PlaneConfiguration G, complementaryFrameTerm κ G τ n := by
  classical
  unfold framePinnedSum
  apply Fintype.sum_equiv (configSdiffEmptyEquiv G)
  intro n
  simp [complementaryFrameTerm, Finset.sdiff_empty, frameSpins_sdiffEmpty]


/-- The edge identity is pointwise and does not require positivity or a proper coloring. -/
theorem fiber_integrand_factorization (κ : Plane → Fin 3) {F B : Finset Plane}
    (hBF : B ⊆ F) (hNo : NoBond (↑B) {z | z ∉ F})
    (unit : ∀ j a, normSq (frameVector j a) = 1)
    (η : FrameBoundary F) (s : PlaneConfiguration B) (n : PlaneConfiguration (F \ B)) :
    planeWeight κ F η (glueConfig s n) = windowWeight κ B s *
      complementaryFrameTerm κ (F \ B) (cutPins κ (F \ B) F B unit η s) n := by
  classical
  let a : Plane → Vec3 := fun z =>
    if z ∈ F then frameVector (κ z) (extendLetters (glueConfig s n) z)
    else frameVector (κ z) (extendBoundary η z)
  let f : Plane × Plane → ℝ := fun e => 1 + dot (a e.1) (a e.2)
  have haF (z : Plane) (hz : z ∈ F) :
      a z = frameVector (κ z) (extendLetters (glueConfig s n) z) := by
    simp [a, hz]
  have haB (z : Plane) (hz : z ∈ B) :
      a z = frameVector (κ z) (extendLetters s z) := by
    simp [a, hBF hz, extendLetters, glueConfig, hz]
  have haG (z : Plane) (hz : z ∈ F \ B) : a z = frameSpins κ n z := by
    obtain ⟨hzF, hzB⟩ := Finset.mem_sdiff.mp hz
    simp [a, hzF, hzB, extendLetters, glueConfig, frameSpins, hz]
  have haExt (z : Plane) (hz : z ∉ F) :
      a z = frameVector (κ z) (extendBoundary η z) := by
    simp [a, hz]
  have hpin (e : originalLegs (F \ B)) :
      (cutPins κ (F \ B) F B unit η s e).val = a e.val.2 := by
    change frameVector (κ e.val.2)
      (if e.val.2 ∈ B then extendLetters s e.val.2 else extendBoundary η e.val.2) = _
    by_cases hzB : e.val.2 ∈ B
    · rw [ite_eq_left hzB]
      exact (haB _ hzB).symm
    · have hzF : e.val.2 ∉ F := by
        intro hzF
        exact ((mem_orig (F \ B) e.val.1 e.val.2).mp e.property).2.1
          (Finset.mem_sdiff.mpr ⟨hzF, hzB⟩)
      rw [ite_eq_right hzB]
      exact (haExt _ hzF).symm
  have hF : planeWeight κ F η (glueConfig s n) = (1 / 12 : ℝ) ^ F.card *
      ((∏ e ∈ internalBonds F, f e) * ∏ e ∈ originalLegs F, f e) := by
    have hi : (∏ e ∈ internalBonds F,
        (1 + dot (frameVector (κ e.1) (extendLetters (glueConfig s n) e.1))
          (frameVector (κ e.2) (extendLetters (glueConfig s n) e.2)))) =
        ∏ e ∈ internalBonds F, f e := by
      apply Finset.prod_congr rfl
      intro e he
      obtain ⟨hx, hy, _⟩ := (mem_bonds F e.1 e.2).mp he
      dsimp [f]
      rw [haF _ hx, haF _ hy]
    have hl : (∏ e ∈ originalLegs F,
        (1 + dot (frameVector (κ e.1) (extendLetters (glueConfig s n) e.1))
          (frameVector (κ e.2) (extendBoundary η e.2)))) =
        ∏ e ∈ originalLegs F, f e := by
      apply Finset.prod_congr rfl
      intro e he
      obtain ⟨hx, hy, _⟩ := (mem_orig F e.1 e.2).mp he
      dsimp [f]
      rw [haF _ hx, haExt _ hy]
    unfold planeWeight
    rw [hi, hl, mul_assoc]
  have hB : windowWeight κ B s = (1 / 12 : ℝ) ^ B.card *
      ∏ e ∈ internalBonds B, f e := by
    unfold windowWeight
    congr 1
    apply Finset.prod_congr rfl
    intro e he
    obtain ⟨hx, hy, _⟩ := (mem_bonds B e.1 e.2).mp he
    dsimp [f]
    rw [haB _ hx, haB _ hy]
  have hG : complementaryFrameTerm κ (F \ B) (cutPins κ (F \ B) F B unit η s) n =
      (1 / 12 : ℝ) ^ (F \ B).card *
        ((∏ e ∈ internalBonds (F \ B), f e) * ∏ e ∈ originalLegs (F \ B), f e) := by
    have hi : (∏ e ∈ internalBonds (F \ B),
        (1 + dot (frameSpins κ n e.1) (frameSpins κ n e.2))) =
        ∏ e ∈ internalBonds (F \ B), f e := by
      apply Finset.prod_congr rfl
      intro e he
      obtain ⟨hx, hy, _⟩ := (mem_bonds (F \ B) e.1 e.2).mp he
      dsimp [f]
      rw [haG _ hx, haG _ hy]
    have hl : (∏ e : originalLegs (F \ B),
        if e.val.1 ∈ F \ B then
          1 + dot (cutPins κ (F \ B) F B unit η s e).val (frameSpins κ n e.val.1)
        else 1) = ∏ e ∈ originalLegs (F \ B), f e := by
      calc
        _ = ∏ e : originalLegs (F \ B), f e.val := by
          apply Finset.prod_congr rfl
          intro e he
          have hx := ((mem_orig (F \ B) e.val.1 e.val.2).mp e.property).1
          rw [ite_eq_left hx, hpin e]
          dsimp [f]
          rw [haG _ hx]
          congr 1
          unfold dot
          exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
        _ = _ := Finset.prod_coe_sort _ _
    unfold complementaryFrameTerm
    rw [hi, hl, mul_assoc]
  have hsymm : ∀ e, f e.swap = f e := by
    intro e
    dsimp [f]
    congr 1
    unfold dot
    exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  have hcard : (1 / 12 : ℝ) ^ F.card =
      (1 / 12 : ℝ) ^ B.card * (1 / 12 : ℝ) ^ (F \ B).card := by
    rw [← pow_add, Nat.add_comm, Finset.card_sdiff_add_card_eq_card hBF]
  rw [hF, hB, hG, split_edge_products hBF hNo f hsymm, hcard]
  ring

/-- Summing the pointwise factorization over the complementary configuration
gives the exact unnormalized window marginal. -/
theorem main : AKLT.Blueprint.Win.FrameFiberSumStatement := by
  classical
  intro _hThree κ _hκ F B hBF hNoBond unit η s
  rw [marginalNumerator_eq_sum_glue hBF η s]
  calc
    (∑ n : PlaneConfiguration (F \ B), planeWeight κ F η (glueConfig s n)) =
        ∑ n : PlaneConfiguration (F \ B),
          windowWeight κ B s *
            complementaryFrameTerm κ (F \ B) (cutPins κ (F \ B) F B unit η s) n := by
          apply Finset.sum_congr rfl
          intro n hn
          exact fiber_integrand_factorization κ hBF hNoBond unit η s n
    _ = windowWeight κ B s *
          (∑ n : PlaneConfiguration (F \ B),
            complementaryFrameTerm κ (F \ B) (cutPins κ (F \ B) F B unit η s) n) := by
          rw [Finset.mul_sum]
    _ = windowWeight κ B s *
          framePinnedSum κ (F \ B) ∅ (cutPins κ (F \ B) F B unit η s) := by
          congr 1
          exact (framePinnedSum_eq_complementaryFrameTerm κ (F \ B)
            (cutPins κ (F \ B) F B unit η s)).symm

end AKLT.W.WIN063
