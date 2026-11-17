module
public import AKLT.Blueprint.Win.Defs

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.Blueprint.Win

/-- `l:cutgeom`, sec5-window.tex:419–439. Use s≥390 and u=s⁴ to establish every inequality in e:sitecutscales; retain the strict predecessor-shell clearance. -/
def CutScalesStatement : Prop :=
  ∀ a y : Plane, ∀ u : ℕ, ∀ i : ℤ, CutSetup a y u i →
    390 ≤ shellSpacing u ∧
    2 * shellSpacing u - 1 ≤ (shellRadius u i : ℝ) ∧
    (shellRadius u i : ℝ) ≤ shellSpacing u ^ 2 ∧
    (shellRadius u i : ℝ) ≤ (u : ℝ) - 31 ∧
    (i - 1 : ℝ) * shellSpacing u <
      (shellRadius u i : ℝ) - shellSpacing u / 12 - 1

/-- `l:cutgeom`, sec5-window.tex:463–486. Intersect the inner square h≥32 with the shell. Each coordinate interval contains a shell endpoint, giving a shell corner; join all remaining side segments to that corner. -/
def CoreConnectedStatement : Prop :=
  ∀ a y : Plane, ∀ u : ℕ, ∀ i : ℤ, CutSetup a y u i →
    ConnectedIn Adjacent (↑(core a y u i)) ∧ core a y u i ⊆ taper a y u i

/-- `l:cutgeom`, sec5-window.tex:441–461. Induct on the natural radial offset. Above k move all maximal coordinates inward; below k move one maximal coordinate outward. Both moves reduce t while preserving h−t≥32. -/
def RadialPathsStatement : Prop :=
  ∀ a y : Plane, ∀ u : ℕ, ∀ i : ℤ, CutSetup a y u i →
    ∀ z ∈ taper a y u i, ∃ w ∈ core a y u i,
      JoinedIn StarAdjacent (↑(taper a y u i)) z w

/-- `l:cutgeom`, sec5-window.tex:488–494. Join each exterior site to the row at height a₂+u+1 along coordinate segments outside the square, then join on that row. -/
def SquareExteriorStatement : Prop :=
  ∀ a : Plane, ∀ u : ℕ, ConnectedIn Adjacent {z | z ∉ square a u}

/-- `l:cutgeom`, sec5-window.tex:494–512. Use the three cases ρ>k+T, ρ<k−T, or h−t<32. Move outward from y, inward to exterior y, or outward from a respectively, with a decreasing termination measure. -/
def ComplementEscapeStatement : Prop :=
  ∀ a y : Plane, ∀ u : ℕ, ∀ i : ℤ, CutSetup a y u i →
    ∀ z : Plane, z ∉ taper a y u i → ∃ w : Plane, w ∉ square a u ∧
      JoinedIn Adjacent {v | v ∉ taper a y u i} z w

/-- `l:cutgeom`, sec5-window.tex:514–529. Window sites have t=0 and h≥65, their neighbours have t≤1 and h≥64. Every tapered site and its neighbours remain beyond the previous radius and inside C. -/
def WindowBufferStatement : Prop :=
  ∀ a y : Plane, ∀ u : ℕ, ∀ i : ℤ, CutSetup a y u i →
    window a y u 64 i ⊆ taper a y u i ∧
    taper a y u i ⊆ farVolume a y u i ∧
    (∀ z ∈ window a y u 64 i, ∀ w, Adjacent z w → w ∈ taper a y u i) ∧
    NoBond (↑(taper a y u i)) {z | z ∉ farVolume a y u i} ∧
    cutRaw a y u i ⊆ cutVolume a y u i

/-- `l:cutgeom`, sec5-window.tex:523–558. Compare a raw-boundary site to a star neighbour in U using the one-Lipschitz h and t. In the near case failure of U forces 30+t≤h<32+t. -/
def RawRangeStatement : Prop :=
  ∀ a y : Plane, ∀ u : ℕ, ∀ i : ℤ, CutSetup a y u i →
    ∀ x ∈ cutRaw a y u i,
    (radialOffset y u i x : ℝ) ≤ shellSpacing u / 12 + 1 ∧
    ((radialOffset y u i x : ℝ) ≤ shellSpacing u / 12 →
      30 + (radialOffset y u i x : ℤ) ≤ squareDepth a u x ∧
      squareDepth a u x < 32 + (radialOffset y u i x : ℤ))

/-- `l:cutgeom`, sec5-window.tex:531–548. Use Gᶜ=B∪Cᶜ∪(C\F): the three sup-distance lower bounds are max(t,65−h), h, and s−1−t. The lattice distance dominates sup-distance. -/
def RawDistanceObstructionsStatement : Prop :=
  ∀ a y : Plane, ∀ u : ℕ, ∀ i : ℤ, CutSetup a y u i →
    ∀ x ∈ cutRaw a y u i,
    min (max (radialOffset y u i x : ℝ) (65 - (squareDepth a u x : ℝ)))
      (min (squareDepth a u x : ℝ)
        (shellSpacing u - 1 - (radialOffset y u i x : ℝ))) ≤
      ((boundaryDepth (cutVolume a y u i) x).toNat : ℝ)

/-- `l:cutgeom`, sec5-window.tex:550–572. Treat t≤T and t>T separately. The integer near depth uses max(t,16)−2, and the far lower bound is T−1; both exceed or equal 14. -/
def RawDepthArithmeticStatement : Prop :=
  ∀ s t h b : ℝ, 390 ≤ s → 0 ≤ t → t ≤ s / 12 + 1 →
    (t ≤ s / 12 → 30 + t ≤ h ∧ h < 32 + t) →
    30 + t ≤ h →
    min (max t (65 - h)) (min h (s - 1 - t)) ≤ b →
    14 ≤ b ∧ (t ≤ s / 12 → max t 16 - 2 ≤ b) ∧
      (s / 12 < t → s / 12 - 1 ≤ b)

/-- `l:cutgeom`, sec5-window.tex:523–525. A star neighbour of U has h≥30+t, by comparing both one-Lipschitz functions to its neighbour in U. State this separately so the far-depth arithmetic does not silently require the near-range premise. -/
def RawHeightStatement : Prop :=
  ∀ a y : Plane, ∀ u : ℕ, ∀ i : ℤ, CutSetup a y u i →
    ∀ x ∈ cutRaw a y u i, 30 + (radialOffset y u i x : ℤ) ≤ squareDepth a u x

/-- `l:cutgeom`, sec5-window.tex:574–616. Use signed depth, separating a shell side inside C, beyond the selected exterior side, or beyond the opposite side. ParallelClearance excludes equality in the first case, and the scale bounds exclude it in the other two. -/
def SignedSideExclusionStatement : Prop :=
  ∀ a y : Plane, ∀ u : ℕ, ∀ i : ℤ, CutSetup a y u i →
    ParallelClearance a y u i → NoCoincidence a y u i

/-- `l:cutgeom`, sec5-window.tex:618–622. Cover one square boundary by four sides; each meets at most the two perpendicular sides of the other. Coincident parallel sides are explicitly excluded. -/
def SquareIntersectionStatement : Prop :=
  ∀ a y : Plane, ∀ r R : ℤ, 0 < r → 0 < R →
    (∀ axis : Fin 2, ∀ ε δ : ℤ, SignedUnit ε → SignedUnit δ →
      coord axis y + ε * r ≠ coord axis a + δ * R) →
    (sphere y r ∩ sphere a R).card ≤ 8

/-- `l:cutgeom`, sec5-window.tex:574–624. At t=j, use radii k±j and at most three integer h-levels in [30+j,32+j). Bound the union of the six sphere intersections by 6×8. -/
def RawLayerCountStatement : Prop :=
  ∀ a y : Plane, ∀ u : ℕ, ∀ i : ℤ, CutSetup a y u i →
    NoCoincidence a y u i →
    (∀ x ∈ cutRaw a y u i, (radialOffset y u i x : ℝ) ≤ shellSpacing u / 12 →
      30 + (radialOffset y u i x : ℤ) ≤ squareDepth a u x ∧
      squareDepth a u x < 32 + (radialOffset y u i x : ℤ)) →
    (∀ a y : Plane, ∀ r R : ℤ, 0 < r → 0 < R →
      (∀ axis : Fin 2, ∀ ε δ : ℤ, SignedUnit ε → SignedUnit δ →
        coord axis y + ε * r ≠ coord axis a + δ * R) →
      (sphere y r ∩ sphere a R).card ≤ 8) →
    ∀ j : ℕ, (j : ℝ) ≤ shellSpacing u / 12 →
      ((cutRaw a y u i).filter fun x => radialOffset y u i x = j).card ≤ 48

/-- `l:cutgeom`, sec5-window.tex:626–634. Split j≤16 from the geometric tail starting at 17. Use summability for θ∈(0,1) and θ/(1−θ)≤1/(1−θ). -/
def NearSeriesStatement : Prop :=
  ∀ θ : ℝ, 0 < θ → θ < 1 →
    Summable (fun j : ℕ => θ ^ (max j 16 - 2)) ∧
    48 * (∑' j : ℕ, θ ^ (max j 16 - 2)) ≤ nearCost θ

/-- `l:cutgeom`, sec5-window.tex:626–639. Group the near finite sum by the natural offset and compare with the nonnegative infinite series. Bound far sites by the containing square cardinality and the real-power depth estimate. -/
def RawWeightSumStatement : Prop :=
  ∀ a y : Plane, ∀ u : ℕ, ∀ i : ℤ, CutSetup a y u i →
    cutRaw a y u i ⊆ square a u →
    (∀ x ∈ cutRaw a y u i,
      ((radialOffset y u i x : ℝ) ≤ shellSpacing u / 12 →
        (max (radialOffset y u i x) 16 - 2 : ℕ) ≤
          (boundaryDepth (cutVolume a y u i) x).toNat) ∧
      (shellSpacing u / 12 < (radialOffset y u i x : ℝ) →
        shellSpacing u / 12 - 1 ≤
          ((boundaryDepth (cutVolume a y u i) x).toNat : ℝ))) →
    (∀ j : ℕ, (j : ℝ) ≤ shellSpacing u / 12 →
      ((cutRaw a y u i).filter fun x => radialOffset y u i x = j).card ≤ 48) →
    ∀ θ : ℝ, 0 < θ → θ < 1 →
    Summable (fun j : ℕ => θ ^ (max j 16 - 2)) →
    48 * (∑' j : ℕ, θ ^ (max j 16 - 2)) ≤ nearCost θ →
    ∑ x ∈ cutRaw a y u i, decay θ (boundaryDepth (cutVolume a y u i) x) ≤
      nearCost θ + tailCost θ u

/-- `l:cutgeom`, sec5-window.tex:641–646. Apply finite-depth Lipschitz at a centre of each cross. Depth at least 13 forces membership in G and excludes its protected layer. -/
def ThickDepthStatement : Prop :=
  ∀ G X₀ : Finset Plane, (∀ x ∈ X₀, 14 ≤ boundaryDepth G x) →
    thicken X₀ ⊆ G ∧ ∀ z ∈ thicken X₀, 13 ≤ boundaryDepth G z

/-- `l:cutgeom`, sec5-window.tex:657–667. The specified pieces partition G\X. Any edge crossing U meets its raw boundary, hence X; the two boundary pin restrictions follow from the two buffers. -/
def CutSeparationStatement : Prop :=
  ∀ F B U X : Finset Plane,
    B ⊆ U → U ⊆ F →
    (∀ z ∈ B, ∀ w, Adjacent z w → w ∈ U) → NoBond (↑U) {z | z ∉ F} →
    rawBoundary U ⊆ X → X ⊆ F \ B →
    SeparatingCut F B X ((U \ B) \ X) ((F \ B) \ (U ∪ X))

end AKLT.Blueprint.Win
