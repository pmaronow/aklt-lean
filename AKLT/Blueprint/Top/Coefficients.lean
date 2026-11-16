import AKLT.Blueprint.Top.Response
import AKLT.Defs.Response

noncomputable section
open AKLT.Defs

namespace AKLT.Blueprint.Top

/-- `l:log-mean-bounds`: positive-variable monotonicity, the exact eight-term enclosure,
and every rational endpoint check for both amended rows. -/
def LogMeanBoundsStatement : Prop :=
  reciprocalLogMean 1 = 1 ∧
  (∀ c : ℝ, 3 / 5 ≤ c → c ≤ 1 → ∀ x x' y y' : ℝ,
    0 < x → x ≤ x' → 0 < y → y ≤ y' →
    1 / (3 * logarithmicMean (c * x') y') - 1 / (5 * logarithmicMean x' y') ≤
      1 / (3 * logarithmicMean (c * x) y) - 1 / (5 * logarithmicMean x y)) ∧
  (∀ c x y : ℝ, 3 / 5 ≤ c → c ≤ 1 → 116 / 125 ≤ x → 1 ≤ y →
    1 / (3 * logarithmicMean (c * x) y) - 1 / (5 * logarithmicMean x y) ≤
      reciprocalLogMean ((116 / 125) * c) / 3 - reciprocalLogMean (116 / 125) / 5) ∧
  (∀ s : ℚ, 0 < s → s < 1 → (logMeanLower s : ℝ) ≤ reciprocalLogMean s ∧
    reciprocalLogMean s ≤ (logMeanUpper s : ℝ)) ∧
  ∀ straight : Bool,
    logMeanUpper ((116 / 125) * localThreshold straight) / 3 - logMeanLower (116 / 125) / 5 ≤
      alphaBound straight ∧
    logMeanUpper ((116 / 125) * localThreshold straight) / 3 ≤ betaBound straight ∧
    logMeanUpper (localThreshold straight) / 3 ≤ betaPrimeBound straight ∧
    0 < betaPrimeBound straight ∧ betaPrimeBound straight ≤ betaBound straight

/-- `l:response`: actual uniform logarithmic identities for the two used U cases,
zero one-bond and D responses, and the free/pinned ratio bounds. -/
def ResponseStatement : Prop :=
  ∀ G : Finset Plane, ∀ τ : PinAssignment G, ∀ D : Network G, D.Auxiliary →
    ∀ y : Plane, D.AdmissibleStart y → ∀ o ∈ D.presentNeighbours y,
    0 < stepRatio D τ false y o ∧ stepRatio D τ false y o ≤ 1 ∧
    0 < stepRatio D τ true y o ∧ stepRatio D τ true y o ≤ 12 / 5 ∧
    (D.status y = .D → stepRatio D τ true y o = 1 ∧ stepRatio D τ false y o = 1) ∧
    (D.status y = .U → (D.presentNeighbours y).card = 1 →
      stepRatio D τ true y o = 1 ∧ stepRatio D τ false y o = 1) ∧
    (∀ f : Plane, D.status y = .U → D.presentNeighbours y = {o, f} → o ≠ f →
      0 < responseBetaPrime D τ y o f ∧ responseBetaPrime D τ y o f ≤ 35510 / 100000 ∧
      Real.log (stepRatio D τ false y o) - Real.log (stepRatio D τ true y o) =
        responseBetaPrime D τ y o f *
          (removedPairMean D τ true y f o - removedPairMean D τ false y f o)) ∧
    ∀ f g : Plane, D.status y = .U → D.presentNeighbours y = {o, f, g} →
      o ≠ f → o ≠ g → f ≠ g →
      0 < responseAlpha D τ y o f g ∧ responseAlpha D τ y o f g ≤ 18094 / 100000 ∧
      0 < responseBeta D τ y o f g ∧ responseBeta D τ y o f g ≤ 36751 / 100000 ∧
      Real.log (stepRatio D τ false y o) - Real.log (stepRatio D τ true y o) =
        responseAlpha D τ y o f g * (removedPairMean D τ true y f g - removedPairMean D τ false y f g) +
        responseBeta D τ y o f g * ((removedPairMean D τ true y f o - removedPairMean D τ false y f o) +
          (removedPairMean D τ true y g o - removedPairMean D τ false y g o))

/-- Legacy full-kept specialization of `l:response-typed`; use V2 below.
Covered U departures satisfy both the analytic and exact
type-dependent bounds, including beta-prime when one non-outgoing neighbour is absent. -/
def ResponseTypedStatement : Prop :=
  H1Statement →
  (∀ straight : Bool, alphaBound straight ≤ 18094 / 100000 ∧
    betaBound straight ≤ 36751 / 100000 ∧ betaPrimeBound straight ≤ 36751 / 100000) ∧
  ∀ G : Finset Plane, ∀ τ : PinAssignment G, ∀ D : Network G, D.Auxiliary →
    ∀ y : Plane, D.AdmissibleStart y → D.status y = .U →
    ∀ incoming outgoing : Compass, CoveredDeparture D y incoming outgoing →
    let o := y + outgoing.step
    let straight := decide (outgoing = incoming)
    (∀ f : Plane, D.presentNeighbours y = {o, f} → o ≠ f →
      0 < responseBetaPrime D τ y o f ∧
      responseBetaPrime D τ y o f ≤ (betaPrimeBound straight : ℝ) ∧
      responseBetaPrime D τ y o f ≤ reciprocalLogMean (localThreshold straight : ℝ) / 3) ∧
    ∀ f g : Plane, D.presentNeighbours y = {o, f, g} → o ≠ f → o ≠ g → f ≠ g →
      0 < responseAlpha D τ y o f g ∧ responseAlpha D τ y o f g ≤ (alphaBound straight : ℝ) ∧
      0 < responseBeta D τ y o f g ∧ responseBeta D τ y o f g ≤ (betaBound straight : ℝ) ∧
      responseBeta D τ y o f g ≤ reciprocalLogMean ((116 / 125) * (localThreshold straight : ℝ)) / 3 ∧
      responseAlpha D τ y o f g ≤ reciprocalLogMean ((116 / 125) * (localThreshold straight : ℝ)) / 3 -
        reciprocalLogMean (116 / 125) / 5 ∧
      responseI D τ true y o f g ≥ (localThreshold straight : ℝ) * responseJ D τ true y f g ∧
      responseI D τ false y o f g ≥ responseJ D τ false y f g ∧
      responseJ D τ false y f g ≥ 1 ∧ responseJ D τ true y f g ≥ 116 / 125

/-- `l:response-typed`: paper-scope internal matching, with all external corner
slots admitted. The original statement remains for proved Rec assemblies. -/
def ResponseTypedStatementV2 : Prop :=
  H1Statement →
  (∀ straight : Bool, alphaBound straight ≤ 18094 / 100000 ∧
    betaBound straight ≤ 36751 / 100000 ∧ betaPrimeBound straight ≤ 36751 / 100000) ∧
  ∀ G : Finset Plane, ∀ τ : PinAssignment G, ∀ D : Network G, D.Auxiliary →
    ∀ y : Plane, D.AdmissibleStart y → D.status y = .U →
    ∀ incoming outgoing : Compass, CoveredDepartureV2 D y incoming outgoing →
    let o := y + outgoing.step
    let straight := decide (outgoing = incoming)
    (∀ f : Plane, D.presentNeighbours y = {o, f} → o ≠ f →
      0 < responseBetaPrime D τ y o f ∧
      responseBetaPrime D τ y o f ≤ (betaPrimeBound straight : ℝ) ∧
      responseBetaPrime D τ y o f ≤ reciprocalLogMean (localThreshold straight : ℝ) / 3) ∧
    ∀ f g : Plane, D.presentNeighbours y = {o, f, g} → o ≠ f → o ≠ g → f ≠ g →
      0 < responseAlpha D τ y o f g ∧ responseAlpha D τ y o f g ≤ (alphaBound straight : ℝ) ∧
      0 < responseBeta D τ y o f g ∧ responseBeta D τ y o f g ≤ (betaBound straight : ℝ) ∧
      responseBeta D τ y o f g ≤ reciprocalLogMean ((116 / 125) * (localThreshold straight : ℝ)) / 3 ∧
      responseAlpha D τ y o f g ≤ reciprocalLogMean ((116 / 125) * (localThreshold straight : ℝ)) / 3 -
        reciprocalLogMean (116 / 125) / 5 ∧
      responseI D τ true y o f g ≥ (localThreshold straight : ℝ) * responseJ D τ true y f g ∧
      responseI D τ false y o f g ≥ responseJ D τ false y f g ∧
      responseJ D τ false y f g ≥ 1 ∧ responseJ D τ true y f g ≥ 116 / 125

end AKLT.Blueprint.Top
