import AKLT.Blueprint.Win.NodesTaper

open AKLT.Defs
open AKLT.Blueprint.Win

namespace AKLT.W.WIN042

private def signValues : Finset ℤ := {1, -1}

private def squareCrossCandidates (a y : Plane) (r R : ℤ) : Finset Plane :=
  ((signValues.product signValues).image fun p =>
    (y.1 + p.1 * r, a.2 + p.2 * R)) ∪
  ((signValues.product signValues).image fun p =>
    (a.1 + p.1 * R, y.2 + p.2 * r))

private lemma supDist_boundary_coordinate {z c : Plane} {r : ℤ}
    (hr : 0 < r) (h : (supDist z c : ℤ) = r) :
    (∃ ε, SignedUnit ε ∧ z.1 = c.1 + ε * r) ∨
    (∃ ε, SignedUnit ε ∧ z.2 = c.2 + ε * r) := by
  have hmax : max |z.1 - c.1| |z.2 - c.2| = r := by
    simpa [supDist, Int.natCast_natAbs, Nat.cast_max] using h
  by_cases hx : |z.1 - c.1| ≥ |z.2 - c.2|
  · have hcoord : |z.1 - c.1| = r := by
      simpa [max_eq_left hx] using hmax
    rcases (abs_eq (le_of_lt hr)).mp hcoord with hpos | hneg
    · left
      refine ⟨1, Or.inl rfl, ?_⟩
      omega
    · left
      refine ⟨-1, Or.inr rfl, ?_⟩
      omega
  · have hy : |z.2 - c.2| ≥ |z.1 - c.1| := le_of_not_ge hx
    have hcoord : |z.2 - c.2| = r := by
      simpa [max_eq_right hy] using hmax
    rcases (abs_eq (le_of_lt hr)).mp hcoord with hpos | hneg
    · right
      refine ⟨1, Or.inl rfl, ?_⟩
      omega
    · right
      refine ⟨-1, Or.inr rfl, ?_⟩
      omega

private lemma mem_vertical_candidates {a y z : Plane} {r R ε δ : ℤ}
    (hε : SignedUnit ε) (hδ : SignedUnit δ)
    (hz₁ : z.1 = y.1 + ε * r) (hz₂ : z.2 = a.2 + δ * R) :
    z ∈ squareCrossCandidates a y r R := by
  apply Finset.mem_union.mpr
  left
  apply Finset.mem_image.mpr
  refine ⟨(ε, δ), Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
  · simpa [signValues, SignedUnit] using hε
  · simpa [signValues, SignedUnit] using hδ
  · exact Prod.ext hz₁.symm hz₂.symm

private lemma mem_horizontal_candidates {a y z : Plane} {r R ε δ : ℤ}
    (hε : SignedUnit ε) (hδ : SignedUnit δ)
    (hz₁ : z.1 = a.1 + δ * R) (hz₂ : z.2 = y.2 + ε * r) :
    z ∈ squareCrossCandidates a y r R := by
  apply Finset.mem_union.mpr
  right
  apply Finset.mem_image.mpr
  refine ⟨(δ, ε), Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
  · simpa [signValues, SignedUnit] using hδ
  · simpa [signValues, SignedUnit] using hε
  · exact Prod.ext hz₁.symm hz₂.symm

private lemma squareCrossCandidates_card_le (a y : Plane) (r R : ℤ) :
    (squareCrossCandidates a y r R).card ≤ 8 := by
  classical
  have hsign : signValues.card = 2 := by norm_num [signValues]
  have hvert :
      (((signValues.product signValues).image fun p =>
        (y.1 + p.1 * r, a.2 + p.2 * R)).card) ≤ 4 := by
    calc
      _ ≤ (signValues.product signValues).card := Finset.card_image_le
      _ = signValues.card * signValues.card := Finset.card_product _ _
      _ = 4 := by norm_num [hsign]
  have hhoriz :
      (((signValues.product signValues).image fun p =>
        (a.1 + p.1 * R, y.2 + p.2 * r)).card) ≤ 4 := by
    calc
      _ ≤ (signValues.product signValues).card := Finset.card_image_le
      _ = signValues.card * signValues.card := Finset.card_product _ _
      _ = 4 := by norm_num [hsign]
  unfold squareCrossCandidates
  calc
    _ ≤ (((signValues.product signValues).image fun p =>
          (y.1 + p.1 * r, a.2 + p.2 * R)).card) +
        (((signValues.product signValues).image fun p =>
          (a.1 + p.1 * R, y.2 + p.2 * r)).card) := Finset.card_union_le _ _
    _ ≤ 4 + 4 := Nat.add_le_add hvert hhoriz
    _ = 8 := by norm_num

theorem main : AKLT.Blueprint.Win.SquareIntersectionStatement := by
  classical
  intro a y r R hr hR hno
  apply Nat.le_trans (Finset.card_le_card ?_)
  · exact squareCrossCandidates_card_le a y r R
  · intro z hz
    rcases Finset.mem_inter.mp hz with ⟨hy, ha⟩
    have hzy : (supDist z y : ℤ) = r := by
      change z ∈ (square y r.toNat).filter (fun w => (supDist w y : ℤ) = r) at hy
      exact (Finset.mem_filter.mp hy).2
    have hza : (supDist z a : ℤ) = R := by
      change z ∈ (square a R.toNat).filter (fun w => (supDist w a : ℤ) = R) at ha
      exact (Finset.mem_filter.mp ha).2
    rcases supDist_boundary_coordinate hr hzy with hyx | hyy
    · rcases hyx with ⟨ε, hε, hye⟩
      rcases supDist_boundary_coordinate hR hza with hax | hay
      · rcases hax with ⟨δ, hδ, hae⟩
        have heq : coord 0 y + ε * r = coord 0 a + δ * R := by
          calc
            coord 0 y + ε * r = y.1 + ε * r := by simp [coord]
            _ = z.1 := hye.symm
            _ = a.1 + δ * R := hae
            _ = coord 0 a + δ * R := by simp [coord]
        exact False.elim ((hno 0 ε δ hε hδ) heq)
      · rcases hay with ⟨δ, hδ, hae⟩
        exact mem_vertical_candidates hε hδ hye hae
    · rcases hyy with ⟨ε, hε, hye⟩
      rcases supDist_boundary_coordinate hR hza with hax | hay
      · rcases hax with ⟨δ, hδ, hae⟩
        exact mem_horizontal_candidates hε hδ hae hye
      · rcases hay with ⟨δ, hδ, hae⟩
        have heq : coord 1 y + ε * r = coord 1 a + δ * R := by
          calc
            coord 1 y + ε * r = y.2 + ε * r := by simp [coord]
            _ = z.2 := hye.symm
            _ = a.2 + δ * R := hae
            _ = coord 1 a + δ * R := by simp [coord]
        exact False.elim ((hno 1 ε δ hε hδ) heq)

end AKLT.W.WIN042
