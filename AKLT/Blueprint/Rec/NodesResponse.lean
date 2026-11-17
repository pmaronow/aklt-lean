module
public import AKLT.Blueprint.Rec.Definitions

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.Blueprint.Rec

/-- `d:domain`, §6 lines 39–48. Reindex the active-site product as a valid
FiniteSpinNetwork, retaining all original legs. The empty network has partition one. -/
def NetworkPositiveStatement : Prop :=
  ∀ G : Finset Plane, ∀ τ : PinAssignment G, ∀ D : Network G,
    D.Auxiliary → ∀ b : Bool, 0 < D.partition τ b (fun _ => 1)

/-- `d:ratios`, §6 lines 259–280. Integrate the unpinned departure spin;
the remaining measure is exactly the departure-deleted network. -/
def ThreeFactorizationStatement : Prop :=
  ∀ a : Departure, a.D.status a.y = .U → ∀ f g : Plane,
    a.D.presentNeighbours a.y = {a.o, f, g} → a.o ≠ f → a.o ≠ g → f ≠ g →
    ∀ b : Bool,
      a.D.partition a.τ b (fun _ => 1) =
        (removeSite a.D a.y).partition a.τ b (fun _ => 1) * responseI a.D a.τ b a.y a.o f g ∧
      (traceStep a.D a.y a.o).partition a.τ b (fun _ => 1) =
        (removeSite a.D a.y).partition a.τ b (fun _ => 1) * responseJ a.D a.τ b a.y f g

/-- `d:ratios`, §6 lines 272–280. Two neighbours give I₂ and post-step scalar one. -/
def TwoFactorizationStatement : Prop :=
  ∀ a : Departure, a.D.status a.y = .U → ∀ f : Plane,
    a.D.presentNeighbours a.y = {a.o, f} → a.o ≠ f → ∀ b : Bool,
      a.D.partition a.τ b (fun _ => 1) =
        (removeSite a.D a.y).partition a.τ b (fun _ => 1) * responseI₂ a.D a.τ b a.y a.o f ∧
      (traceStep a.D a.y a.o).partition a.τ b (fun _ => 1) =
        (removeSite a.D a.y).partition a.τ b (fun _ => 1)

/-- `l:response`, §6 lines 339–364. Condition on every other spin. Distinct
neighbours are nonadjacent, unpinned, and have at most three remaining factors.
Use the three-factor mean bound; do not assert arbitrary-function covariance. -/
def RemovedMeanIntervalsStatement : Prop :=
  ∀ a : Departure, a.D.status a.y = .U → ∀ f g : Plane,
    a.D.presentNeighbours a.y = {a.o, f, g} → a.o ≠ f → a.o ≠ g → f ≠ g →
    (∀ b : Bool,
      41 / 50 ≤ responseI a.D a.τ b a.y a.o f g ∧
      responseI a.D a.τ b a.y a.o f g ≤ 34 / 25 ∧
      116 / 125 ≤ responseJ a.D a.τ b a.y f g ∧
      responseJ a.D a.τ b a.y f g ≤ 134 / 125) ∧
    1 ≤ responseJ a.D a.τ false a.y f g ∧
    responseJ a.D a.τ false a.y f g ≤ responseI a.D a.τ false a.y a.o f g

/-- `l:response`, §6 lines 393–408. The analogous two-neighbour fibre estimate. -/
def TwoMeanIntervalsStatement : Prop :=
  ∀ a : Departure, a.D.status a.y = .U → ∀ f : Plane,
    a.D.presentNeighbours a.y = {a.o, f} → a.o ≠ f →
    (∀ b : Bool, 22 / 25 ≤ responseI₂ a.D a.τ b a.y a.o f ∧
      responseI₂ a.D a.τ b a.y a.o f ≤ 28 / 25) ∧
    1 ≤ responseI₂ a.D a.τ false a.y a.o f

/-- `l:response`, §6 lines 360–367. Degree-four free positivity after removal.
Each inserted endpoint has lost its bond to y. -/
def FreeRemovedPairStatement : Prop :=
  ∀ a : Departure, ∀ f ∈ a.D.presentNeighbours a.y, ∀ g ∈ a.D.presentNeighbours a.y, f ≠ g →
    0 ≤ removedPairMean a.D a.τ false a.y f g

/-- `l:response`, §6 lines 303–317. Positive logarithmic mean, its min/max
bounds, and its divided-difference identity, including the diagonal. -/
def LogMeanBasicStatement : Prop :=
  ∀ x y : ℝ, 0 < x → 0 < y →
    0 < logarithmicMean x y ∧ min x y ≤ logarithmicMean x y ∧
    logarithmicMean x y ≤ max x y ∧
    Real.log x - Real.log y = (x - y) / logarithmicMean x y

/-- `l:response`, §6 lines 311–317. Integrate along the line segment to
obtain monotonicity, including equal endpoints. -/
def LogMeanMonotoneStatement : Prop :=
  ∀ x x' y y' : ℝ, 0 < x → x ≤ x' → 0 < y → y ≤ y' →
    logarithmicMean x y ≤ logarithmicMean x' y'

/-- `l:response`, §6 lines 371–386. Integrate the two-term geometric
identity and bound its remainder. All denominators are positive for 0<s<1. -/
def CrudeLogEnclosureStatement : Prop :=
  ∀ s : ℚ, 0 < s → s < 1 → reciprocalLogMean s ≤ (crudeLogUpper s : ℝ)

/-- `l:response`, §6 lines 421–435. Trace validity and positive network
normalizers imply strictly positive ratios for both pin choices. -/
def StepRatioPositiveStatement : Prop :=
  ∀ a : Departure, ∀ b : Bool, 0 < stepRatio a.D a.τ b a.y a.o

/-- `l:response`, §6 lines 410–420. Integrate the departure; free scalar
products are nonnegative, so the free post-step partition is no larger. -/
def FreeRatioUpperStatement : Prop :=
  ∀ a : Departure, stepRatio a.D a.τ false a.y a.o ≤ 1

/-- `l:response`, §6 lines 421–431. Pointwise I≥1/2 and J≤6/5 for three
neighbours; the two- and one-neighbour cases are smaller. -/
def PinnedRatioUpperStatement : Prop :=
  ∀ a : Departure, stepRatio a.D a.τ true a.y a.o ≤ 12 / 5

/-- `d:ratios`, §6 lines 272–280. A D departure has at most one bond,
no original legs, and its site integral is one. -/
def DStepTrivialStatement : Prop :=
  ∀ a : Departure, a.D.status a.y = .D →
    stepRatio a.D a.τ true a.y a.o = 1 ∧ stepRatio a.D a.τ false a.y a.o = 1

/-- `l:response`, §6 lines 406–408. A U site with only its outgoing bond
has both pre- and post-step integrated factor one. -/
def OneStepTrivialStatement : Prop :=
  ∀ a : Departure, a.D.status a.y = .U → (a.D.presentNeighbours a.y).card = 1 →
    stepRatio a.D a.τ true a.y a.o = 1 ∧ stepRatio a.D a.τ false a.y a.o = 1

/-- `l:response`, §6 lines 393–408. Positive I₂ arguments give beta-prime>0. -/
def BetaPrimePositiveStatement : Prop :=
  ∀ a : Departure, a.D.status a.y = .U → ∀ f : Plane,
    a.D.presentNeighbours a.y = {a.o, f} → a.o ≠ f →
    0 < responseBetaPrime a.D a.τ a.y a.o f

/-- `l:response`, §6 lines 393–408. Apply the crude enclosure at 22/25
and clear its positive rational denominator. -/
def BetaPrimeUniformStatement : Prop :=
  ∀ a : Departure, a.D.status a.y = .U → ∀ f : Plane,
    a.D.presentNeighbours a.y = {a.o, f} → a.o ≠ f →
    responseBetaPrime a.D a.τ a.y a.o f ≤ 35510 / 100000

/-- `l:response`, §6 lines 393–408. Divide the two integrated partitions;
apply the positive divided difference to I₂, including coincident values. -/
def TwoLogIdentityStatement : Prop :=
  ∀ a : Departure, a.D.status a.y = .U → ∀ f : Plane,
    a.D.presentNeighbours a.y = {a.o, f} → a.o ≠ f →
    Real.log (stepRatio a.D a.τ false a.y a.o) - Real.log (stepRatio a.D a.τ true a.y a.o) =
      responseBetaPrime a.D a.τ a.y a.o f * pairResponse a.D a.τ a.y f a.o

/-- `l:response`, §6 lines 365–370. L_I≤34/25 and L_J≥116/125 give
alpha≥175/5916; no optimized coefficient hypothesis is needed. -/
def AlphaPositiveStatement : Prop :=
  ∀ a : Departure, a.D.status a.y = .U → ∀ f g : Plane,
    a.D.presentNeighbours a.y = {a.o, f, g} → a.o ≠ f → a.o ≠ g → f ≠ g →
    0 < responseAlpha a.D a.τ a.y a.o f g

/-- `l:response`, §6 lines 387–391. Bound beta at 41/50 and subtract
25/134 from it. Clear positive denominators to obtain the crude alpha. -/
def AlphaUniformStatement : Prop :=
  ∀ a : Departure, a.D.status a.y = .U → ∀ f g : Plane,
    a.D.presentNeighbours a.y = {a.o, f, g} → a.o ≠ f → a.o ≠ g → f ≠ g →
    responseAlpha a.D a.τ a.y a.o f g ≤ 18094 / 100000

/-- `l:response`, §6 lines 365–370. Positive I arguments imply beta>0. -/
def BetaPositiveStatement : Prop :=
  ∀ a : Departure, a.D.status a.y = .U → ∀ f g : Plane,
    a.D.presentNeighbours a.y = {a.o, f, g} → a.o ≠ f → a.o ≠ g → f ≠ g →
    0 < responseBeta a.D a.τ a.y a.o f g

/-- `l:response`, §6 lines 387–391. Logarithmic-mean monotonicity and
the crude enclosure at 41/50 give beta≤36751/100000. -/
def BetaUniformStatement : Prop :=
  ∀ a : Departure, a.D.status a.y = .U → ∀ f g : Plane,
    a.D.presentNeighbours a.y = {a.o, f, g} → a.o ≠ f → a.o ≠ g → f ≠ g →
    responseBeta a.D a.τ a.y a.o f g ≤ 36751 / 100000

/-- `l:response`, §6 lines 319–336. Subtract log(J/I) in the two pin
choices and collect the three scalar-product responses. -/
def ThreeLogIdentityStatement : Prop :=
  ∀ a : Departure, a.D.status a.y = .U → ∀ f g : Plane,
    a.D.presentNeighbours a.y = {a.o, f, g} → a.o ≠ f → a.o ≠ g → f ≠ g →
    Real.log (stepRatio a.D a.τ false a.y a.o) - Real.log (stepRatio a.D a.τ true a.y a.o) =
      responseAlpha a.D a.τ a.y a.o f g * pairResponse a.D a.τ a.y f g +
      responseBeta a.D a.τ a.y a.o f g *
        (pairResponse a.D a.τ a.y f a.o + pairResponse a.D a.τ a.y g a.o)

/-- The crude rational arithmetic is a small exact check, not a numerical log evaluation. -/
def CrudeRationalStatement : Prop :=
  crudeLogUpper (41 / 50) / 3 ≤ 367502 / 10^6 ∧
  crudeLogUpper (22 / 25) / 3 ≤ 35510 / 100000 ∧
  (367502 / 10^6 - 25 / 134 : ℚ) ≤ 18094 / 100000

theorem crudeRational : CrudeRationalStatement := by
  norm_num [CrudeRationalStatement, crudeLogUpper]

end AKLT.Blueprint.Rec
