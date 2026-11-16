import AKLT.Blueprint.Q.NodesEnergy

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Challenge AKLT.Blueprint.Q

namespace AKLT.W.Q050

attribute [local instance] Classical.propDecidable

def glueConfig {W V : Finset Plane} (_hVW : V ⊆ W)
    (σ : PlaneConfiguration W) (v : PlaneConfiguration V) : PlaneConfiguration W :=
  fun x => if hx : (x : Plane) ∈ V then v ⟨x, hx⟩ else σ x

private theorem mem_internal (W : Finset Plane) (e : Plane × Plane) :
    e ∈ internalBonds W ↔
      e.1 ∈ W ∧ e.2 ∈ W ∧ e.2 ∈ positiveNeighbours e.1 := by
  rcases e with ⟨x, y⟩
  simp [internalBonds, and_assoc, and_left_comm, and_comm]

private theorem mem_leg (W : Finset Plane) (e : Plane × Plane) :
    e ∈ originalLegs W ↔
      e.1 ∈ W ∧ e.2 ∉ W ∧ e.2 ∈ neighbours e.1 := by
  rcases e with ⟨x, y⟩
  simp [originalLegs, and_assoc, and_left_comm, and_comm]

private theorem mem_neighbours (x y : Plane) :
    y ∈ neighbours x ↔ y ∈ positiveNeighbours x ∨ x ∈ positiveNeighbours y := by
  simp only [neighbours, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨d, rfl⟩
    cases d <;> simp [positiveNeighbours, Compass.step, Prod.add_def]
  · intro h
    simp only [positiveNeighbours, Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with (rfl | rfl) | h | h
    · exact ⟨.east, by simp [Compass.step, Prod.add_def]⟩
    · exact ⟨.north, by simp [Compass.step, Prod.add_def]⟩
    · subst x
      exact ⟨.west, by simp [Compass.step, Prod.add_def]⟩
    · subst x
      exact ⟨.south, by simp [Compass.step, Prod.add_def]⟩

private theorem not_positive_reverse {x y : Plane}
    (h : y ∈ positiveNeighbours x) : x ∉ positiveNeighbours y := by
  rcases x with ⟨x1, x2⟩
  rcases y with ⟨y1, y2⟩
  simp only [positiveNeighbours, Finset.mem_insert, Finset.mem_singleton,
    Prod.mk.injEq] at h ⊢
  omega

/-- Canonical orientation of an edge, regardless of which endpoint is in the volume. -/
private def orient (e : Plane × Plane) : Plane × Plane :=
  if e.2 ∈ positiveNeighbours e.1 then e else e.swap

private theorem orient_eq_imp {e f : Plane × Plane} (h : orient e = orient f) :
    e = f ∨ e = f.swap := by
  by_cases he : e.2 ∈ positiveNeighbours e.1 <;>
    by_cases hf : f.2 ∈ positiveNeighbours f.1
  · exact Or.inl (by simpa [orient, he, hf] using h)
  · exact Or.inr (by simpa [orient, he, hf] using h)
  · right
    have hh : e.swap = f := by simpa [orient, he, hf] using h
    simpa using congrArg Prod.swap hh
  · left
    have hh : e.swap = f.swap := by simpa [orient, he, hf] using h
    simpa using congrArg Prod.swap hh

private theorem orient_inj (W : Finset Plane) :
    Set.InjOn orient (↑(originalLegs W) : Set (Plane × Plane)) := by
  intro e he f hf h
  rcases orient_eq_imp h with h | h
  · exact h
  · have he' := (mem_leg W e).mp he
    have hf' := (mem_leg W f).mp hf
    exact (hf'.2.1 (by simpa [h] using he'.1)).elim

private theorem mem_oriented_legs (W : Finset Plane) (e : Plane × Plane) :
    e ∈ (originalLegs W).image orient ↔
      e.2 ∈ positiveNeighbours e.1 ∧
        ((e.1 ∈ W ∧ e.2 ∉ W) ∨ (e.2 ∈ W ∧ e.1 ∉ W)) := by
  constructor
  · intro h
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp h
    obtain ⟨hf1, hf2, hfn⟩ := (mem_leg W f).mp hf
    by_cases hp : f.2 ∈ positiveNeighbours f.1
    · simp [orient, hp, hf1, hf2]
    · have hr := (mem_neighbours f.1 f.2).mp hfn
      have hr' : f.1 ∈ positiveNeighbours f.2 := hr.resolve_left hp
      simp [orient, hp, hr', hf1, hf2]
  · rintro ⟨hp, (⟨h1, h2⟩ | ⟨h2, h1⟩)⟩
    · refine Finset.mem_image.mpr ⟨e, ?_, ?_⟩
      · exact (mem_leg W e).mpr ⟨h1, h2, (mem_neighbours _ _).mpr (Or.inl hp)⟩
      · simp [orient, hp]
    · refine Finset.mem_image.mpr ⟨e.swap, ?_, ?_⟩
      · exact (mem_leg W e.swap).mpr
          ⟨h2, h1, (mem_neighbours _ _).mpr (Or.inr hp)⟩
      · simp [orient, not_positive_reverse hp]

/-- Every nearest-neighbour edge meeting a volume, counted in positive orientation. -/
private def volumeEdges (W : Finset Plane) : Finset (Plane × Plane) :=
  internalBonds W ∪ (originalLegs W).image orient

private theorem mem_volumeEdges (W : Finset Plane) (e : Plane × Plane) :
    e ∈ volumeEdges W ↔
      e.2 ∈ positiveNeighbours e.1 ∧ (e.1 ∈ W ∨ e.2 ∈ W) := by
  simp only [volumeEdges, Finset.mem_union, mem_internal, mem_oriented_legs]
  tauto

private theorem volumeEdges_mono {V W : Finset Plane} (hVW : V ⊆ W) :
    volumeEdges V ⊆ volumeEdges W := by
  intro e he
  obtain ⟨hp, h1 | h2⟩ := (mem_volumeEdges V e).mp he
  · exact (mem_volumeEdges W e).mpr ⟨hp, Or.inl (hVW h1)⟩
  · exact (mem_volumeEdges W e).mpr ⟨hp, Or.inr (hVW h2)⟩

private theorem disjoint_edges (W : Finset Plane) :
    Disjoint (internalBonds W) ((originalLegs W).image orient) := by
  apply Finset.disjoint_left.mpr
  intro e hi hl
  obtain ⟨h1, h2, _⟩ := (mem_internal W e).mp hi
  obtain ⟨_, h | h⟩ := (mem_oriented_legs W e).mp hl
  · exact h.2 h2
  · exact h.2 h1

/-- A single site letter, with the actual volume and exterior boundary filled in. -/
private def filledLetters (W : Finset Plane) (η : FrameBoundary W)
    (σ : PlaneConfiguration W) (x : Plane) : IcoLetter :=
  if x ∈ W then extendLetters σ x else extendBoundary η x

private def edgeFactor (κ : Plane → Fin 3) (a : Plane → IcoLetter)
    (e : Plane × Plane) : ℝ :=
  1 + dot (frameVector (κ e.1) (a e.1)) (frameVector (κ e.2) (a e.2))

private theorem edgeFactor_swap (κ : Plane → Fin 3) (a : Plane → IcoLetter)
    (e : Plane × Plane) : edgeFactor κ a e.swap = edgeFactor κ a e := by
  unfold edgeFactor dot
  simp only [Prod.fst_swap, Prod.snd_swap]
  congr 1
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

private theorem edgeFactor_orient (κ : Plane → Fin 3) (a : Plane → IcoLetter)
    (e : Plane × Plane) : edgeFactor κ a (orient e) = edgeFactor κ a e := by
  unfold orient
  split_ifs
  · rfl
  · exact edgeFactor_swap κ a e

private theorem planeWeight_edges (κ : Plane → Fin 3) (W : Finset Plane)
    (η : FrameBoundary W) (σ : PlaneConfiguration W) :
    planeWeight κ W η σ = (1 / 12 : ℝ) ^ W.card *
      ∏ e ∈ volumeEdges W, edgeFactor κ (filledLetters W η σ) e := by
  have hi : (∏ e ∈ internalBonds W,
      (1 + dot (frameVector (κ e.1) (extendLetters σ e.1))
        (frameVector (κ e.2) (extendLetters σ e.2)))) =
      ∏ e ∈ internalBonds W, edgeFactor κ (filledLetters W η σ) e := by
    apply Finset.prod_congr rfl
    intro e he
    obtain ⟨h1, h2, _⟩ := (mem_internal W e).mp he
    simp [edgeFactor, filledLetters, h1, h2]
  have hl : (∏ e ∈ originalLegs W,
      (1 + dot (frameVector (κ e.1) (extendLetters σ e.1))
        (frameVector (κ e.2) (extendBoundary η e.2)))) =
      ∏ e ∈ originalLegs W, edgeFactor κ (filledLetters W η σ) e := by
    apply Finset.prod_congr rfl
    intro e he
    obtain ⟨h1, h2, _⟩ := (mem_leg W e).mp he
    simp [edgeFactor, filledLetters, h1, h2]
  unfold planeWeight
  rw [hi, hl, volumeEdges, Finset.prod_union (disjoint_edges W),
    Finset.prod_image (orient_inj W)]
  simp_rw [edgeFactor_orient]
  ring

private theorem mem_exteriorSites (V : Finset Plane) (x : Plane) :
    x ∈ exteriorSites V ↔ x ∉ V ∧ ∃ y ∈ V, x ∈ neighbours y := by
  constructor
  · intro hx
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨h1, h2, hn⟩ := (mem_leg V e).mp he
    exact ⟨h2, e.1, h1, hn⟩
  · rintro ⟨hx, y, hy, hn⟩
    exact Finset.mem_image.mpr ⟨(y, x), (mem_leg V _).mpr ⟨hy, hx, hn⟩, rfl⟩

private theorem volumeEdges_endpoints {V : Finset Plane} {e : Plane × Plane}
    (he : e ∈ volumeEdges V) :
    (e.1 ∈ V ∨ e.1 ∈ exteriorSites V) ∧ (e.2 ∈ V ∨ e.2 ∈ exteriorSites V) := by
  obtain ⟨hp, hm⟩ := (mem_volumeEdges V e).mp he
  constructor
  · by_cases h1 : e.1 ∈ V
    · exact Or.inl h1
    · right
      exact (mem_exteriorSites V _).mpr
        ⟨h1, e.2, hm.resolve_left h1, (mem_neighbours _ _).mpr (Or.inr hp)⟩
  · by_cases h2 : e.2 ∈ V
    · exact Or.inl h2
    · right
      exact (mem_exteriorSites V _).mpr
        ⟨h2, e.1, hm.resolve_right h2, (mem_neighbours _ _).mpr (Or.inl hp)⟩

private theorem filledLetters_glue {W V : Finset Plane} (hVW : V ⊆ W)
    (η : FrameBoundary W) (σ : PlaneConfiguration W) (v : PlaneConfiguration V)
    (x : Plane) :
    filledLetters W η (glueConfig hVW σ v) x =
      if x ∈ V then extendLetters v x else filledLetters W η σ x := by
  by_cases hxV : x ∈ V
  · have hxW := hVW hxV
    simp [filledLetters, glueConfig, extendLetters, hxV, hxW]
  · by_cases hxW : x ∈ W <;>
      simp [filledLetters, glueConfig, extendLetters, hxV, hxW]

private theorem filledLetters_induced {W V : Finset Plane} (hVW : V ⊆ W)
    (η : FrameBoundary W) (σ : PlaneConfiguration W) (v : PlaneConfiguration V)
    (x : Plane) (hx : x ∈ V ∨ x ∈ exteriorSites V) :
    filledLetters W η (glueConfig hVW σ v) x =
      filledLetters V (inducedBoundary W V η σ) v x := by
  rw [filledLetters_glue]
  by_cases hxV : x ∈ V
  · simp [filledLetters, hxV]
  · have hxE := hx.resolve_left hxV
    simp [filledLetters, hxV, extendBoundary, hxE, inducedBoundary]

private theorem edgeFactor_induced {W V : Finset Plane} (hVW : V ⊆ W)
    (κ : Plane → Fin 3) (η : FrameBoundary W) (σ : PlaneConfiguration W)
    (v : PlaneConfiguration V) (e : Plane × Plane) (he : e ∈ volumeEdges V) :
    edgeFactor κ (filledLetters W η (glueConfig hVW σ v)) e =
      edgeFactor κ (filledLetters V (inducedBoundary W V η σ) v) e := by
  obtain ⟨h1, h2⟩ := volumeEdges_endpoints he
  unfold edgeFactor
  rw [filledLetters_induced hVW η σ v e.1 h1,
    filledLetters_induced hVW η σ v e.2 h2]

private theorem edgeFactor_fixed {W V : Finset Plane} (hVW : V ⊆ W)
    (κ : Plane → Fin 3) (η : FrameBoundary W) (σ : PlaneConfiguration W)
    (v : PlaneConfiguration V) (e : Plane × Plane)
    (he : e ∈ volumeEdges W \ volumeEdges V) :
    edgeFactor κ (filledLetters W η (glueConfig hVW σ v)) e =
      edgeFactor κ (filledLetters W η σ) e := by
  obtain ⟨heW, heV⟩ := Finset.mem_sdiff.mp he
  have hp := ((mem_volumeEdges W e).mp heW).1
  have h1 : e.1 ∉ V := fun h => heV ((mem_volumeEdges V e).mpr ⟨hp, Or.inl h⟩)
  have h2 : e.2 ∉ V := fun h => heV ((mem_volumeEdges V e).mpr ⟨hp, Or.inr h⟩)
  simp only [edgeFactor, filledLetters_glue, ite_eq_right h1, ite_eq_right h2]

/-- Splitting the edge product leaves a multiplier independent of the interior letters.
This identity needs no geometric frame separation or interaction bounds. -/
theorem fiberWeightFactorization (κ : Plane → Fin 3) (W : Finset Plane)
    (η : FrameBoundary W) (V : Finset Plane) (hVW : V ⊆ W)
    (σ : PlaneConfiguration W) :
    ∃ c : ℝ, ∀ v : PlaneConfiguration V,
      planeWeight κ W η (glueConfig hVW σ v) =
        c * planeWeight κ V (inducedBoundary W V η σ) v := by
  let C : ℝ := ∏ e ∈ volumeEdges W \ volumeEdges V,
    edgeFactor κ (filledLetters W η σ) e
  refine ⟨(1 / 12 : ℝ) ^ (W.card - V.card) * C, ?_⟩
  intro v
  have hprod :
      (∏ e ∈ volumeEdges W, edgeFactor κ (filledLetters W η (glueConfig hVW σ v)) e) =
        C * ∏ e ∈ volumeEdges V,
          edgeFactor κ (filledLetters V (inducedBoundary W V η σ) v) e := by
    rw [← Finset.prod_sdiff (volumeEdges_mono hVW)]
    congr 1
    · exact Finset.prod_congr rfl (fun e he => edgeFactor_fixed hVW κ η σ v e he)
    · exact Finset.prod_congr rfl (fun e he => edgeFactor_induced hVW κ η σ v e he)
  have hcard : (1 / 12 : ℝ) ^ W.card =
      (1 / 12 : ℝ) ^ (W.card - V.card) * (1 / 12 : ℝ) ^ V.card := by
    rw [← pow_add, Nat.sub_add_cancel (Finset.card_le_card hVW)]
  rw [planeWeight_edges, planeWeight_edges, hprod, hcard]
  ring

end AKLT.W.Q050
