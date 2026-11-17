module
public import AKLT.W.GAP037.Geometry

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Challenge AKLT.Blueprint.Gap
attribute [local instance] Classical.propDecidable
namespace AKLT.W.GAP037
local instance (α : Type) : DecidableEq α := Classical.decEq α

/-- An antiferromagnetic factor at a frozen torus bond. -/
def torusFactor {L N : Size} (κ : Site L N → Fin 3)
    (σ : TorusConfiguration L N) (b : Bond L N) : ℝ :=
  1 - dot (frameVector (κ b.1) (σ b.1))
    (frameVector (κ (nextSite b.1 b.2)) (σ (nextSite b.1 b.2)))

/-- A plane factor, using the same total assignment at internal and crossing edges. -/
def planeFactor (κ : Plane → Fin 3) (W : Finset Plane) (η : Plane → IcoLetter)
    (ρ : PlaneConfiguration W) (e : Plane × Plane) : ℝ :=
  1 + dot (frameVector (κ e.1) (insertBlock W η ρ e.1))
    (frameVector (κ e.2) (insertBlock W η ρ e.2))

theorem torusFactor_endpoints {L N : Size} (κ : Site L N → Fin 3)
    (σ : TorusConfiguration L N) (b : Bond L N) (x y : Site L N)
    (h : bondSites b = {x,y}) :
    torusFactor κ σ b = 1 - dot (frameVector (κ x) (σ x)) (frameVector (κ y) (σ y)) := by
  rcases pair_eq_pair_cases h with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · unfold torusFactor
    rw [h2,h1]
  · unfold torusFactor
    rw [h2,h1,dot_comm]

/-- The plane weight is the product over the single combined edge set. -/
theorem planeWeight_edges (κ : Plane → Fin 3) (W : Finset Plane)
    (η : Plane → IcoLetter) (ρ : PlaneConfiguration W) :
    planeWeight κ W (fun z => η z) ρ =
      (1/12 : ℝ)^W.card * ∏ e ∈ planeEdges W, planeFactor κ W η ρ e := by
  unfold planeWeight planeEdges
  rw [Finset.prod_union (planeEdges_disjoint W), ← mul_assoc]
  apply congrArg₂ (· * ·)
  · apply congrArg ((1/12 : ℝ)^W.card * ·)
    apply Finset.prod_congr rfl
    intro e he
    have hd := (mem_internalBonds W e).mp he
    simp [planeFactor,extendLetters,insertBlock,hd.1,hd.2.1]
  · apply Finset.prod_congr rfl
    intro e he
    have hd := (mem_originalLegs W e).mp he
    have hb : e.2 ∈ exteriorSites W := Finset.mem_image.mpr ⟨e,he,rfl⟩
    simp [planeFactor,extendLetters,extendBoundary,insertBlock,hd.1,hd.2.1,hb]

/-- The coordinate data give the signed spin identity at every endpoint used by a plane factor. -/
theorem gauge_vector {L N : Size} {M : ℕ} {a : Site L N}
    {κ : Site L N → Fin 3} (C : BoxCoordinates L N M a κ)
    (hB : LiftBonds L N M C.centre) (σ : TorusConfiguration L N)
    (ω : (x : torusSquare L N M a) → IcoLetter) (z : Plane)
    (hz : z ∈ square C.centre M ∨ z ∈ exteriorSites (square C.centre M)) :
    frameVector (κ (reduction L N z))
      (insertBlock (square C.centre M) (C.boundary σ) (C.change.configurations ω) z) =
    paritySign z • frameVector (κ (reduction L N z))
      (insertBlock (torusSquare L N M a) σ ω (reduction L N z)) := by
  rcases hz with hz | hz
  · let x := C.change.sites.symm ⟨z,hz⟩
    have hx : C.change.sites x = ⟨z,hz⟩ := by simp [x]
    have hp : reduction L N z = x.val := by simpa only [hx] using C.site_reduces x
    have hv := C.vector_change ω x
    rw [hx] at hv
    simpa [insertBlock,hz,hp] using hv
  · have hd := exteriorSites_data hz
    obtain ⟨x,hx,hxz⟩ := hd.2
    have hhalo := adjacent_in_halo hx hxz
    have hout : reduction L N z ∉ torusSquare L N M a := by
      rw [← coordinates_image C]
      intro h
      exact hd.1 ((hB.2.2 z hhalo).mp h)
    simpa [insertBlock,hd.1,hout] using C.boundary_vector σ z hz

/-- The two lifted parity signs turn each local antiferromagnetic factor into its plane factor. -/
theorem gauge_factor {L N : Size} {M : ℕ} {a : Site L N}
    {κ : Site L N → Fin 3} (C : BoxCoordinates L N M a κ)
    (hB : LiftBonds L N M C.centre) (σ : TorusConfiguration L N)
    (ω : (x : torusSquare L N M a) → IcoLetter)
    (e : Plane × Plane) (he : e ∈ planeEdges (square C.centre M)) :
    planeFactor (κ ∘ reduction L N) (square C.centre M) (C.boundary σ)
      (C.change.configurations ω) e =
    torusFactor κ (insertBlock (torusSquare L N M a) σ ω) (edgeBond L N e) := by
  have hd := planeEdges_data he
  rw [torusFactor_endpoints κ _ _ _ _ (edgeBond_sites L N hd.2)]
  unfold planeFactor
  simp only [Function.comp_apply]
  rw [gauge_vector C hB σ ω e.1 (Or.inl hd.1),
    gauge_vector C hB σ ω e.2 (planeEdges_second he), dot_gauge hd.2]
  ring

/-- Reindex all local factors by the exact lifted bonds. -/
theorem gauge_product {L N : Size} {M : ℕ} {a : Site L N}
    {κ : Site L N → Fin 3} (C : BoxCoordinates L N M a κ)
    (hB : LiftBonds L N M C.centre)
    (hI : Set.InjOn (reduction L N) (↑(square C.centre (M+1)) : Set Plane))
    (σ : TorusConfiguration L N) (ω : (x : torusSquare L N M a) → IcoLetter) :
    (∏ e ∈ planeEdges (square C.centre M),
      planeFactor (κ ∘ reduction L N) (square C.centre M) (C.boundary σ)
        (C.change.configurations ω) e) =
    ∏ b ∈ localBonds (torusSquare L N M a),
      torusFactor κ (insertBlock (torusSquare L N M a) σ ω) b := by
  apply Finset.prod_bij (fun e _ => edgeBond L N e)
  · intro e he
    rw [← coordinates_image C]
    exact edgeBond_local he
  · intro e he f hf hef
    exact edgeBond_injective L N M C.centre hI he hf hef
  · intro b hb
    obtain ⟨e,he,heb⟩ := edgeBond_surjective L N M C.centre hB b (by rwa [coordinates_image C])
    exact ⟨e,he,heb⟩
  · intro e he
    exact gauge_factor C hB σ ω e he

/-- All torus interaction factors are strictly positive under the supplied hypotheses. -/
theorem torusFactor_pos
    (hPositive : ∀ i j : Fin 3, i ≠ j → ∀ a b : IcoLetter,
      0 < 1 + dot (frameVector i a) (frameVector j b) ∧
      0 < 1 - dot (frameVector i a) (frameVector j b))
    {L N : Size} (κ : Site L N → Fin 3) (hκ : ProperTorusColouring κ)
    (σ : TorusConfiguration L N) (b : Bond L N) : 0 < torusFactor κ σ b :=
  (hPositive _ _ (hκ b) _ _).2

theorem torusWeight_pos
    (hPositive : ∀ i j : Fin 3, i ≠ j → ∀ a b : IcoLetter,
      0 < 1 + dot (frameVector i a) (frameVector j b) ∧
      0 < 1 - dot (frameVector i a) (frameVector j b))
    {L N : Size} (κ : Site L N → Fin 3) (hκ : ProperTorusColouring κ)
    (σ : TorusConfiguration L N) : 0 < torusWeight L N κ σ := by
  apply mul_pos
  · exact Finset.prod_pos (by intros; norm_num)
  · exact Finset.prod_pos (fun b hb => torusFactor_pos hPositive κ hκ σ b)

/-- Factors outside the block do not depend on its free coordinates. -/
theorem exterior_factor {L N : Size} (κ : Site L N → Fin 3)
    (Q : Finset (Site L N)) (σ : TorusConfiguration L N) (ω : (x : Q) → IcoLetter)
    (b : Bond L N) (hb : ¬Touches Q b) :
    torusFactor κ (insertBlock Q σ ω) b = torusFactor κ σ b := by
  have hb1 : b.1 ∉ Q := fun h => hb (Or.inl h)
  have hb2 : nextSite b.1 b.2 ∉ Q := fun h => hb (Or.inr h)
  simp [torusFactor,insertBlock,hb1,hb2]

/-- The raw weights differ by a strictly positive scalar independent of the free assignment.
The scalar contains exactly the exterior-only interactions and the ratio of constant site weights. -/
theorem liftedWeightFactorization
    (hPositive : ∀ i j : Fin 3, i ≠ j → ∀ a b : IcoLetter,
      0 < 1 + dot (frameVector i a) (frameVector j b) ∧
      0 < 1 - dot (frameVector i a) (frameVector j b))
    {L N : Size} {M : ℕ} {a : Site L N} {κ : Site L N → Fin 3}
    (hκ : ProperTorusColouring κ) (C : BoxCoordinates L N M a κ)
    (hB : LiftBonds L N M C.centre)
    (hI : Set.InjOn (reduction L N) (↑(square C.centre (M+1)) : Set Plane))
    (σ : TorusConfiguration L N) :
    ∃ c : ℝ, 0 < c ∧ ∀ ω : (x : torusSquare L N M a) → IcoLetter,
      torusWeight L N κ (insertBlock (torusSquare L N M a) σ ω) =
        c * planeWeight (κ ∘ reduction L N) (square C.centre M)
          (fun z => C.boundary σ z) (C.change.configurations ω) := by
  let Q := torusSquare L N M a
  let T : ℝ := ∏ _x : Site L N, (1/12 : ℝ)
  let P : ℝ := (1/12 : ℝ)^(square C.centre M).card
  let E : ℝ := ∏ b ∈ Finset.univ.filter (fun b : Bond L N => ¬Touches Q b), torusFactor κ σ b
  have hT : 0 < T := Finset.prod_pos (by intros; norm_num)
  have hP : 0 < P := pow_pos (by norm_num) _
  have hE : 0 < E := Finset.prod_pos (fun b hb => torusFactor_pos hPositive κ hκ σ b)
  refine ⟨T * E / P, div_pos (mul_pos hT hE) hP, ?_⟩
  intro ω
  have hext : (∏ b ∈ Finset.univ.filter (fun b : Bond L N => ¬Touches Q b),
      torusFactor κ (insertBlock Q σ ω) b) = E := by
    apply Finset.prod_congr rfl
    intro b hb
    exact exterior_factor κ Q σ ω b (Finset.mem_filter.mp hb).2
  have ht : torusWeight L N κ (insertBlock Q σ ω) =
      T * ((∏ b ∈ localBonds Q, torusFactor κ (insertBlock Q σ ω) b) * E) := by
    change T * (∏ b, torusFactor κ (insertBlock Q σ ω) b) = _
    rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (Touches Q)
      (torusFactor κ (insertBlock Q σ ω)), hext]
    rfl
  have hp : planeWeight (κ ∘ reduction L N) (square C.centre M)
      (fun z => C.boundary σ z) (C.change.configurations ω) =
      P * (∏ b ∈ localBonds Q, torusFactor κ (insertBlock Q σ ω) b) := by
    rw [planeWeight_edges, gauge_product C hB hI σ ω]
  rw [ht,hp]
  field_simp [ne_of_gt hP]

end AKLT.W.GAP037
