module
public import AKLT.Blueprint.Gap.NodesFinite
public import AKLT.Defs.FrameModel
public import AKLT.Blueprint.Q.Definitions

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Gap

namespace AKLT.W.GAP011

private lemma adjacent_of_mem_neighbours {x y : Plane} (hy : y ∈ neighbours x) :
    Adjacent x y := by
  classical
  rcases Finset.mem_image.mp hy with ⟨d, -, hxy⟩
  subst y
  cases d <;> simp [Adjacent, latticeDist, Compass.step]

private lemma adjacent_of_mem_positiveNeighbours {x y : Plane}
    (hy : y ∈ positiveNeighbours x) : Adjacent x y := by
  simp only [positiveNeighbours, Finset.mem_insert, Finset.mem_singleton] at hy
  rcases hy with hy | hy
  · rw [hy]
    simp [Adjacent, latticeDist]
  · rw [hy]
    simp [Adjacent, latticeDist]

private lemma original_endpoints {W : Finset Plane} {e : Plane × Plane}
    (he : e ∈ originalLegs W) : e.1 ∈ W ∧ e.2 ∉ W ∧ Adjacent e.1 e.2 := by
  classical
  rcases Finset.mem_biUnion.mp he with ⟨x, hx, hxe⟩
  rcases Finset.mem_image.mp hxe with ⟨y, hy, hxy⟩
  have hy' := Finset.mem_sdiff.mp hy
  have hAdj := adjacent_of_mem_neighbours hy'.1
  subst e
  exact ⟨hx, hy'.2, hAdj⟩

private lemma internal_adjacent {W : Finset Plane} {e : Plane × Plane}
    (he : e ∈ internalBonds W) : Adjacent e.1 e.2 := by
  classical
  rcases Finset.mem_biUnion.mp he with ⟨x, hx, hxe⟩
  rcases Finset.mem_image.mp hxe with ⟨y, hy, hxy⟩
  have hyN := adjacent_of_mem_positiveNeighbours (Finset.mem_inter.mp hy).1
  subst e
  exact hyN

private lemma boundary_factor_pos
    (hframe : ∀ i j : Fin 3, i ≠ j → ∀ a b : IcoLetter,
      0 < 1 + dot (frameVector i a) (frameVector j b))
    {κ : Plane → Fin 3} (hκ : ProperPlaneColouring κ)
    {W : Finset Plane} (η : FrameBoundary W) {e : Plane × Plane}
    (he : e ∈ originalLegs W) (a : IcoLetter) :
    0 < 1 + dot (frameVector (κ e.1) a)
      (frameVector (κ e.2) (extendBoundary η e.2)) := by
  have hcol := hκ e.1 e.2 (original_endpoints he).2.2
  exact hframe _ _ hcol a (extendBoundary η e.2)

private lemma planeSiteWeight_pos
    (hframe : ∀ i j : Fin 3, i ≠ j → ∀ a b : IcoLetter,
      0 < 1 + dot (frameVector i a) (frameVector j b))
    {κ : Plane → Fin 3} (hκ : ProperPlaneColouring κ)
    {W : Finset Plane} (η : FrameBoundary W) (x : W) (a : IcoLetter) :
    0 < AKLT.Blueprint.Q.planeSiteWeight κ W η x a := by
  unfold AKLT.Blueprint.Q.planeSiteWeight
  apply mul_pos (by norm_num)
  apply Finset.prod_pos
  intro e he
  simp only [Finset.mem_filter] at he
  simpa [he.2] using boundary_factor_pos hframe hκ η he.1 a

private lemma positive_normalize_probability {α : Type*} [Fintype α] [Nonempty α]
    (w : Weight α) (hw : ∀ a, 0 < w a) : PositiveProbability (normalize w) := by
  have hsum : 0 < ∑ a, w a :=
    Finset.sum_pos (fun a _ => hw a) Finset.univ_nonempty
  constructor
  · intro a
    exact div_pos (hw a) hsum
  · simp only [AKLT.Defs.normalize]
    rw [← Finset.sum_div]
    exact div_self hsum.ne'

private lemma product_probability {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ x, Fintype (S x)]
    (π : (x : ι) → Weight (S x)) (hπ : ∀ x, PositiveProbability (π x)) :
    PositiveProbability (fun σ : (x : ι) → S x => ∏ x : ι, π x (σ x)) := by
  constructor
  · intro σ
    apply Finset.prod_pos
    intro x hx
    exact (hπ x).1 (σ x)
  · calc
      (∑ σ : (x : ι) → S x, ∏ x : ι, π x (σ x)) = ∏ x : ι, ∑ a, π x a := by
        rw [← Fintype.prod_sum]
      _ = 1 := by
        have hs : ∀ x : ι, (∑ a, π x a) = 1 := fun x => (hπ x).2
        simp [hs]

private lemma product_boundary_factorization
    (κ : Plane → Fin 3) (W : Finset Plane) (η : FrameBoundary W)
    (σ : PlaneConfiguration W) :
    (∏ x : W, AKLT.Blueprint.Q.planeSiteWeight κ W η x (σ x)) =
      (1 / 12 : ℝ) ^ W.card *
        (∏ e ∈ originalLegs W,
          (1 + dot (frameVector (κ e.1) (extendLetters σ e.1))
            (frameVector (κ e.2) (extendBoundary η e.2)))) := by
  classical
  have hmap : ∀ e ∈ originalLegs W, e.1 ∈ W := fun e he => (original_endpoints he).1
  have hfib := Finset.prod_fiberwise_of_maps_to
    (s := originalLegs W) (t := W) (g := fun e : Plane × Plane => e.1) hmap
      (fun e => 1 + dot (frameVector (κ e.1) (extendLetters σ e.1))
        (frameVector (κ e.2) (extendBoundary η e.2)))
  have hlocal : ∀ x : W,
      (∏ e ∈ (originalLegs W).filter (fun e => e.1 = x.val),
        (1 + dot (frameVector (κ x.val) (σ x)) (frameVector (κ e.2) (extendBoundary η e.2)))) =
      (∏ e ∈ (originalLegs W).filter (fun e => e.1 = x.val),
        (1 + dot (frameVector (κ e.1) (extendLetters σ e.1))
          (frameVector (κ e.2) (extendBoundary η e.2)))) := by
    intro x
    apply Finset.prod_congr rfl
    intro e he
    have he' := Finset.mem_filter.mp he
    simp [extendLetters, he'.2]
  calc
    (∏ x : W, AKLT.Blueprint.Q.planeSiteWeight κ W η x (σ x)) =
        (∏ x : W, (1 / 12 : ℝ)) *
          ∏ x : W, ∏ e ∈ (originalLegs W).filter (fun e => e.1 = x.val),
            (1 + dot (frameVector (κ x.val) (σ x))
              (frameVector (κ e.2) (extendBoundary η e.2))) := by
      simp only [AKLT.Blueprint.Q.planeSiteWeight]
      rw [Finset.prod_mul_distrib]
    _ = (1 / 12 : ℝ) ^ W.card *
          ∏ x : W, ∏ e ∈ (originalLegs W).filter (fun e => e.1 = x.val),
            (1 + dot (frameVector (κ e.1) (extendLetters σ e.1))
              (frameVector (κ e.2) (extendBoundary η e.2))) := by
      congr 1
      · simp [Finset.prod_const]
      · apply Finset.prod_congr rfl
        intro x hx
        exact hlocal x
    _ = (1 / 12 : ℝ) ^ W.card *
          ∏ x ∈ W, ∏ e ∈ (originalLegs W).filter (fun e => e.1 = x),
            (1 + dot (frameVector (κ e.1) (extendLetters σ e.1))
              (frameVector (κ e.2) (extendBoundary η e.2))) := by
      congr 1
      exact Finset.prod_coe_sort W (fun x =>
        ∏ e ∈ (originalLegs W).filter (fun e => e.1 = x),
          (1 + dot (frameVector (κ e.1) (extendLetters σ e.1))
            (frameVector (κ e.2) (extendBoundary η e.2))) )
    _ = (1 / 12 : ℝ) ^ W.card *
          ∏ e ∈ originalLegs W,
            (1 + dot (frameVector (κ e.1) (extendLetters σ e.1))
              (frameVector (κ e.2) (extendBoundary η e.2))) := by
      rw [hfib]

theorem main : AKLT.Blueprint.Gap.FrameProductReferenceStatement := by
  intro hframe κ hκ W η
  let hsite : (x : W) → Weight IcoLetter :=
    fun x => AKLT.Blueprint.Q.planeSiteWeight κ W η x
  have hsite_pos : ∀ x a, 0 < hsite x a := by
    intro x a
    exact planeSiteWeight_pos hframe hκ η x a
  let π : (x : W) → Weight IcoLetter := fun x => normalize (hsite x)
  have hπ : ∀ x, PositiveProbability (π x) := by
    intro x
    apply positive_normalize_probability
    exact hsite_pos x
  let q : PlaneConfiguration W → ℝ := fun σ => ∏ x : W, π x (σ x)
  let raw : PlaneConfiguration W → ℝ := fun σ => ∏ x : W, hsite x (σ x)
  let C : ℝ := ∏ x : W, ∑ a : IcoLetter, hsite x a
  have hC : 0 < C := by
    dsimp [C]
    apply Finset.prod_pos
    intro x hx
    apply Finset.sum_pos
    · intro a ha
      exact hsite_pos x a
    · exact Finset.univ_nonempty
  have href : ∀ σ, q σ = raw σ / C := by
    intro σ
    simp [q, raw, C, π, hsite, AKLT.Defs.normalize, Finset.prod_div_distrib]
  have hq : PositiveProbability q := by
    exact product_probability π hπ
  have hinteraction : ∀ σ, 0 < planeInteraction κ W σ := by
    intro σ
    unfold planeInteraction
    apply Finset.prod_pos
    intro e he
    have hcol := hκ e.1 e.2 (internal_adjacent he)
    exact hframe _ _ hcol (extendLetters σ e.1) (extendLetters σ e.2)
  have hfactor : ∀ σ, planeWeight κ W η σ = C * (q σ * planeInteraction κ W σ) := by
    intro σ
    have hraw := product_boundary_factorization κ W η σ
    have hraw' : raw σ = (1 / 12 : ℝ) ^ W.card *
        (∏ e ∈ originalLegs W,
          (1 + dot (frameVector (κ e.1) (extendLetters σ e.1))
            (frameVector (κ e.2) (extendBoundary η e.2)))) := by
      simpa [raw, hsite] using hraw
    have hwp : planeWeight κ W η σ = raw σ * planeInteraction κ W σ := by
      rw [planeWeight, planeInteraction]
      rw [hraw']
      ring
    rw [hwp, href σ]
    field_simp [ne_of_gt hC]
  let Z : ℝ := expectation q (planeInteraction κ W)
  have hZ : 0 < Z := by
    dsimp [Z, expectation]
    apply Finset.sum_pos
    · intro σ hσ
      exact mul_pos (hq.1 σ) (hinteraction σ)
    · exact Finset.univ_nonempty
  have hpartition : (∑ σ, planeWeight κ W η σ) = C * Z := by
    dsimp [Z, expectation]
    calc
      (∑ σ, planeWeight κ W η σ) = ∑ σ, C * (q σ * planeInteraction κ W σ) := by
        apply Finset.sum_congr rfl
        intro σ hσ
        exact hfactor σ
      _ = C * ∑ σ, q σ * planeInteraction κ W σ := (Finset.mul_sum _ _ _).symm
  refine ⟨π, hπ, Z, hZ, rfl, ?_⟩
  intro σ
  rw [planeLaw, AKLT.Defs.normalize, hfactor σ, hpartition]
  dsimp [q]
  field_simp [ne_of_gt hC, ne_of_gt hZ]

end AKLT.W.GAP011
