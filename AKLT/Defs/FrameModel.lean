module
public import AKLT.Defs.Polynomial
public import AKLT.Defs.Probability

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators

namespace AKLT.Defs

/-- `d:framemodel`: a proper plane coloring is quantified, not assumed translation invariant. -/
def ProperPlaneColouring (κ : Plane → Fin 3) : Prop :=
  ∀ x y, Adjacent x y → κ x ≠ κ y

/-- `d:framemodel`: proper coloring on the actual frozen torus bonds. -/
def ProperTorusColouring {L N : AKLT.Challenge.Size}
    (κ : AKLT.Challenge.Site L N → Fin 3) : Prop :=
  ∀ e : AKLT.Challenge.Bond L N, κ e.1 ≠ κ (AKLT.Challenge.nextSite e.1 e.2)

/-- A finite configuration of actual frame-letter labels. -/
abbrev PlaneConfiguration (W : Finset Plane) := (x : W) → IcoLetter

/-- The finite exterior neighbor sites; a boundary uses one letter per site. -/
def exteriorSites (W : Finset Plane) : Finset Plane := (originalLegs W).image Prod.snd

/-- `d:framemodel`: admissible boundaries, distinct from unrelated original-leg pins. -/
abbrev FrameBoundary (W : Finset Plane) := (z : exteriorSites W) → IcoLetter

/-- Extension outside the requested finite configuration is used only for indexing.
All interactions in a partition product use sites of its actual configuration. -/
def extendLetters {W : Finset Plane} (σ : PlaneConfiguration W) (x : Plane) : IcoLetter :=
  if h : x ∈ W then σ ⟨x, h⟩ else (0, 0, 0)

/-- Finite boundary extension for leg indexing. -/
def extendBoundary {W : Finset Plane} (η : FrameBoundary W) (x : Plane) : IcoLetter :=
  if h : x ∈ exteriorSites W then η ⟨x, h⟩ else (0, 0, 0)

/-- `d:framemodel`: the unnormalized ferromagnetic plane specification. -/
def planeWeight (κ : Plane → Fin 3) (W : Finset Plane) (η : FrameBoundary W)
    (σ : PlaneConfiguration W) : ℝ :=
  (1 / 12 : ℝ) ^ W.card *
  (∏ e ∈ internalBonds W, (1 + dot (frameVector (κ e.1) (extendLetters σ e.1))
      (frameVector (κ e.2) (extendLetters σ e.2)))) *
  ∏ e ∈ originalLegs W, (1 + dot (frameVector (κ e.1) (extendLetters σ e.1))
      (frameVector (κ e.2) (extendBoundary η e.2)))

/-- `d:framemodel`: the normalized plane law, with its actual normalizer. -/
def planeLaw (κ : Plane → Fin 3) (W : Finset Plane) (η : FrameBoundary W) :
    Weight (PlaneConfiguration W) := normalize (planeWeight κ W η)

/-- Finite pushforward, used for window marginals. -/
def marginal {Ω Ξ : Type*} [Fintype Ω] [DecidableEq Ξ]
    (p : Weight Ω) (r : Ω → Ξ) : Weight Ξ := fun z => ∑ x, if r x = z then p x else 0

/-- `d:W`: the actual B marginal; there is no identification across alphabets. -/
def planeMarginal (κ : Plane → Fin 3) (W B : Finset Plane) (η : FrameBoundary W) :
    Weight (PlaneConfiguration B) :=
  marginal (planeLaw κ W η) (fun σ x => extendLetters σ x.val)

/-- `d:framemodel`: finite torus frame configurations. -/
abbrev TorusConfiguration (L N : AKLT.Challenge.Size) := AKLT.Challenge.Site L N → IcoLetter

/-- `d:framemodel`: antiferromagnetic torus weight with one factor per frozen bond. -/
def torusWeight (L N : AKLT.Challenge.Size) (κ : AKLT.Challenge.Site L N → Fin 3)
    (σ : TorusConfiguration L N) : ℝ :=
  (∏ _x : AKLT.Challenge.Site L N, (1 / 12 : ℝ)) *
    ∏ e : AKLT.Challenge.Bond L N,
      (1 - dot (frameVector (κ e.1) (σ e.1))
        (frameVector (κ (AKLT.Challenge.nextSite e.1 e.2)) (σ (AKLT.Challenge.nextSite e.1 e.2))))

/-- `d:framemodel`: the normalized all-parity torus law. -/
def torusLaw (L N : AKLT.Challenge.Size) (κ : AKLT.Challenge.Site L N → Fin 3) :
    Weight (TorusConfiguration L N) := normalize (torusWeight L N κ)

/-- `l:tight`: unnormalized product reference weight, including the factor five per site. -/
def torusReference (L N : AKLT.Challenge.Size) : Weight (TorusConfiguration L N) :=
  fun _ => ∏ _x : AKLT.Challenge.Site L N, (5 / 12 : ℝ)

/-- `l:tight`: evaluation at the finitely chosen frame spinors. -/
def frameEval {L N : AKLT.Challenge.Size} (κ : AKLT.Challenge.Site L N → Fin 3)
    (ψ : AKLT.Challenge.Hilbert L N) (σ : TorusConfiguration L N) : ℂ :=
  physicalEval ψ (fun x => frameSpinor (κ x) (σ x))

/-- `d:W`: the entire uniform physical-site window property, with all colorings and translates. -/
def WindowProperty (l₀ : ℕ) (p₀ : ℝ) (Mstar : ℕ) : Prop :=
  1 ≤ l₀ ∧ 1 ≤ Mstar ∧ 0 < p₀ ∧ p₀ ≤ 1 ∧
  ∀ κ : Plane → Fin 3, ProperPlaneColouring κ → ∀ a : Plane,
    ∀ u : ℕ, Mstar ≤ u → ∀ y : Plane,
    setDistance supDist y (↑(square a u) : Set Plane) = 1 →
    ∀ i : ℤ, 2 ≤ i → (i : ℝ) ≤ shellSpacing u → i ∉ exceptionalIndices a y u →
    ∀ η ξ : FrameBoundary (farVolume a y u i),
      totalVariation (planeMarginal κ (farVolume a y u i) (window a y u l₀ i) η)
        (planeMarginal κ (farVolume a y u i) (window a y u l₀ i) ξ) ≤ 1 - p₀

end AKLT.Defs
