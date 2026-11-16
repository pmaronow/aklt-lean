import AKLT.Defs.Pattern

noncomputable section
open scoped BigOperators

namespace AKLT.Defs

/-- `l:log-mean-bounds`: logarithmic mean, with its continuous diagonal value. -/
def logarithmicMean (x y : ℝ) : ℝ := if x = y then x else (x - y) / (Real.log x - Real.log y)

/-- `l:log-mean-bounds`: reciprocal logarithmic mean against one, including f(1)=1. -/
def reciprocalLogMean (s : ℝ) : ℝ := (logarithmicMean s 1)⁻¹

/-- The eight-term exact lower enclosure. -/
def logMeanLower (s : ℚ) : ℚ :=
  let t := (1 - s) / (1 + s)
  2 / (1 - s) * ∑ k ∈ Finset.range 8, t ^ (2 * k + 1) / (2 * k + 1 : ℚ)

/-- The exact rational remainder in the upper enclosure. -/
def logMeanUpper (s : ℚ) : ℚ :=
  let t := (1 - s) / (1 + s)
  logMeanLower s + 2 * t^17 / (17 * (1 - t^2) * (1 - s))

/-- `d:ratios`: removal of the departure site, with every original pin unchanged. -/
def removeSite {G : Finset Plane} (D : Network G) (y : Plane) : Network G :=
  { D with status := Function.update D.status y .X }

/-- `d:ratios`: actual step partition quotient in the mass-free convention. -/
def stepRatio {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (pinned : Bool) (y o : Plane) : ℝ := traceRatio D τ pinned [y, o]

/-- A pair expectation in the departure-deleted network. -/
def removedPairMean {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (pinned : Bool) (y a b : Plane) : ℝ :=
  (removeSite D y).expectation τ pinned (fun n => dot (n a) (n b))

/-- `d:ratios`: I for the three-present-neighbour case. -/
def responseI {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (pinned : Bool) (y o f g : Plane) : ℝ :=
  1 + (removedPairMean D τ pinned y f g + removedPairMean D τ pinned y f o +
    removedPairMean D τ pinned y g o) / 3

/-- `d:ratios`: J for the three-present-neighbour case. -/
def responseJ {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (pinned : Bool) (y f g : Plane) : ℝ := 1 + removedPairMean D τ pinned y f g / 5

/-- `l:response`: the actual beta coefficient obtained by the logarithmic-mean identity. -/
def responseBeta {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (y o f g : Plane) : ℝ :=
  1 / (3 * logarithmicMean (responseI D τ true y o f g) (responseI D τ false y o f g))

/-- `l:response`: the actual alpha coefficient, without an optimized constant hypothesis. -/
def responseAlpha {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (y o f g : Plane) : ℝ := responseBeta D τ y o f g -
      1 / (5 * logarithmicMean (responseJ D τ true y f g) (responseJ D τ false y f g))

/-- `l:response`: beta-prime for exactly two present neighbours. -/
def responseBetaPrime {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (y o f : Plane) : ℝ := 1 / (3 * logarithmicMean
      (1 + removedPairMean D τ true y f o / 3) (1 + removedPairMean D τ false y f o / 3))

/-- Rotation sending the canonical incoming north direction to the actual direction. -/
def normalizeRotation (a : Compass) (z : Plane) : Plane :=
  match a with
  | .north => z | .east => (z.2, -z.1) | .south => (-z.1, -z.2) | .west => (-z.2, z.1)

/-- Legacy full-kept matching, retained for existing Rec proofs.
The paper-scope matcher is `CoveredDepartureV2` below.
Covering tips are intentionally not constrained by any global tip kept set. -/
def CoveredDeparture {G : Finset Plane} (D : Network G) (y : Plane) (incoming outgoing : Compass) : Prop :=
  ∃ π : PatternData, π.Covered ∧ normalizeRotation incoming π.outgoing.step = outgoing.step ∧
    ∀ z ∈ templateSites \ templateTips,
      π.statusAt z = D.status (y + normalizeRotation incoming z) ∧
      (π.statusAt z ≠ .X →
        (π.keptAt z).image (fun t => y + normalizeRotation incoming t) =
          D.kept (y + normalizeRotation incoming z))

/-- Internal template-bond presence, independent of its chosen positive orientation. -/
def PatternData.InternalPresent (π : PatternData) (z t : Plane) : Prop :=
  (z, t) ∈ π.bonds ∨ (t, z) ∈ π.bonds

/-- `l:local`, `l:response-typed`, corrected paper scope: match non-tip statuses
and actual internal bonds. External directions are slot factors, never matching
requirements on global kept sets. A covering tip may add an absent actual bond
(its effective field is then zero), but must retain every present actual bond.
The original `CoveredDeparture` is retained for existing Rec proofs. -/
def CoveredDepartureV2 {G : Finset Plane} (D : Network G) (y : Plane)
    (incoming outgoing : Compass) : Prop :=
  let chart := fun z => y + normalizeRotation incoming z
  ∃ π : PatternData, π.Covered ∧ normalizeRotation incoming π.outgoing.step = outgoing.step ∧
    (∀ z ∈ templateSites \ templateTips, π.statusAt z = D.status (chart z)) ∧
    ∀ z ∈ templateSites \ templateTips, ∀ t ∈ templateSites,
      if t ∈ templateTips then D.Present (chart z) (chart t) → π.InternalPresent z t
      else (π.InternalPresent z t ↔ D.Present (chart z) (chart t))

end AKLT.Defs
