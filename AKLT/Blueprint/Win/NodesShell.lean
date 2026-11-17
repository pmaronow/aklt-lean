import AKLT.Blueprint.Win.Defs

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.Blueprint.Win

/-- `l:shellgeom`, sec5-window.tex:50–58. Square the two square-root identities; use s≥16 to bound the low-degree terms and Int.floor bounds. -/
def ShellScaleStatement : Prop :=
  ∀ l u : ℕ, 1 ≤ l → geometryThreshold l ≤ u →
    16 ≤ shellSpacing u ∧ 6 * ((l : ℝ) + 1) ≤ shellSpacing u ∧
    shellSpacing u ^ 4 = (u : ℝ) ∧
    shellSpacing u ^ 2 + 4 * shellSpacing u / 3 < (u : ℝ) ∧
    shellSpacing u ^ 2 + shellSpacing u < (u : ℝ) / 2 ∧
    2 * shellSpacing u / 3 < (⌊shellSpacing u⌋ : ℤ)

/-- `l:shellgeom`, sec5-window.tex:40–76. Translate and use signed coordinate permutations to put the exterior site on the bottom edge. Only one corner can have radius below u. -/
def CloseCornerStatement : Prop :=
  ∀ a y : Plane, ∀ u : ℕ,
    setDistance supDist y (↑(square a u) : Set Plane) = 1 →
    ((squareCorners a u).filter fun c => supDist c y < u).card ≤ 1

/-- `l:shellgeom`, sec5-window.tex:58–70. Apply the sup-distance triangle inequality and k_i≤s²+s to every exceptional witness. Retain its radial error as well as its corner. -/
def ExceptionalLocalizationStatement : Prop :=
  ∀ a y : Plane, ∀ u : ℕ,
    shellSpacing u ^ 2 + 4 * shellSpacing u / 3 < (u : ℝ) →
    ∀ i ∈ exceptionalIndices a y u, ∃ c ∈ squareCorners a u,
      supDist c y < u ∧
      |(supDist c y : ℝ) - (shellRadius u i : ℝ)| < shellSpacing u / 3

/-- `l:shellgeom`, sec5-window.tex:72–76. Use floor(x+s)≥floor(x)+floor(s), and floor(s)>2s/3 for s≥16. -/
def RadiusGapStatement : Prop :=
  ∀ u : ℕ, 16 ≤ shellSpacing u → ∀ i j : ℤ, i < j →
    2 * shellSpacing u / 3 < (shellRadius u j - shellRadius u i : ℝ)

/-- `l:shellgeom`, sec5-window.tex:64–76. The unique close corner cannot approximate two radii separated by more than 2s/3. Apply Finset.card_le_one. -/
def ExceptionalCountStatement : Prop :=
  ∀ a y : Plane, ∀ u : ℕ,
    ((squareCorners a u).filter fun c => supDist c y < u).card ≤ 1 →
    (∀ i ∈ exceptionalIndices a y u, ∃ c ∈ squareCorners a u,
      supDist c y < u ∧
      |(supDist c y : ℝ) - (shellRadius u i : ℝ)| < shellSpacing u / 3) →
    (∀ i j : ℤ, i < j →
      2 * shellSpacing u / 3 < (shellRadius u j - shellRadius u i : ℝ)) →
    (exceptionalIndices a y u).card ≤ 1

/-- `l:shellgeom`, sec5-window.tex:78–100. Normalize the exterior side. A vertical side with insufficient parallel clearance has a lowest shell point within s/3 of a bottom corner; horizontal sides already have large clearance. -/
def SideCornerWitnessStatement : Prop :=
  ∀ l : ℕ, ∀ a y : Plane, ∀ u : ℕ, ShellSetup l a y u →
    ∀ i : ℤ, 2 ≤ i → i ≤ lastShellIndex u →
    ¬ ParallelClearance a y u i → i ∈ exceptionalIndices a y u

/-- `l:shellgeom`, sec5-window.tex:102–108. Cover the near layer by the eight intersections of shell sides with perpendicular exterior strips. Parallel intersections are excluded by clearance and s/3>l. -/
def NearShellCountStatement : Prop :=
  ∀ l : ℕ, ∀ a y : Plane, ∀ u : ℕ, ShellSetup l a y u →
    ∀ i : ℤ, 2 ≤ i → i ≤ lastShellIndex u →
    ParallelClearance a y u i → (nearShell a y u l i).card ≤ 8 * l

/-- `l:shellgeom`, sec5-window.tex:110–111. For s≥2, floor(i s)≥i s−1>(i−1)s. Membership filters then give inclusion. -/
def ShellInclusionStatement : Prop :=
  ∀ a y : Plane, ∀ u : ℕ, 2 ≤ shellSpacing u →
    ∀ i : ℤ, 2 ≤ i → shell a y u i ⊆ farVolume a y u i

/-- `l:shellgeom`, sec5-window.tex:112–123. Extract a distance-one witness in F_i. Sup-distance is 1-Lipschitz, so integrality pins the old radius to floor((i−1)s). Empty F_i has infinite distance. -/
def PredecessorShellStatement : Prop :=
  ∀ a y : Plane, ∀ u : ℕ, ∀ i : ℤ, 2 ≤ i →
    ∀ x ∈ square a u \ farVolume a y u i,
      setDistance supDist x (↑(farVolume a y u i) : Set Plane) ≤ 1 →
        x ∈ shell a y u (i - 1)

/-- `l:shellgeom`, sec5-window.tex:120–123. Every remaining point has radius >(i−1)s≥s>1. The infimum over an empty set is top. -/
def SeedSeparationStatement : Prop :=
  ∀ a y : Plane, ∀ u : ℕ, 2 ≤ shellSpacing u → ∀ i : ℤ, 2 ≤ i →
    ¬ setDistance supDist y (↑(farVolume a y u i) : Set Plane) ≤ 1

end AKLT.Blueprint.Win
