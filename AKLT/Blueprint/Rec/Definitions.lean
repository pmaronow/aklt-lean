module
public import AKLT.Blueprint.Top.Coefficients

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

/-! Concrete data used by the §6–§7 blueprint. No proof obligations are fields
of these definitions except the ordinary mathematical premises of an instance. -/

noncomputable section
open scoped BigOperators ENNReal
open AKLT.Defs

namespace AKLT.Blueprint.Rec

/-- `d:pattern`, §6 lines 488–519. Compare kept flags inside the original volume.
Directions leaving G are original leg slots, not members of `Network.kept`.
This repairs the exact-set comparison in `Defs.CoveredDeparture`. -/
def CoveredDepartureV2 {G : Finset Plane} (D : Network G) (y : Plane)
    (incoming outgoing : Compass) : Prop :=
  ∃ π : PatternData, π.Covered ∧
    normalizeRotation incoming π.outgoing.step = outgoing.step ∧
    ∀ z ∈ templateSites \ templateTips,
      π.statusAt z = D.status (y + normalizeRotation incoming z) ∧
      (π.statusAt z ≠ .X →
        (π.keptAt z).image (fun t => y + normalizeRotation incoming t) ∩ G =
          D.kept (y + normalizeRotation incoming z))

/-- One admissible step. Proof fields record only hypotheses in `l:response`. -/
structure Departure where
  G : Finset Plane
  τ : PinAssignment G
  D : Network G
  y : Plane
  o : Plane
  auxiliary : D.Auxiliary
  start : D.AdmissibleStart y
  present : o ∈ D.presentNeighbors y

/-- The pinned-minus-free scalar-product response after deleting the passage site. -/
def pairResponse {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (y a b : Plane) : ℝ :=
  removedPairMean D τ true y a b - removedPairMean D τ false y a b

/-- The two-neighbor pre-step scalar, with post-step scalar one. -/
def responseI₂ {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (pinned : Bool) (y o f : Plane) : ℝ :=
  1 + removedPairMean D τ pinned y f o / 3

/-- The finite rational enclosure used for the crude bounds in §6, lines 371–408. -/
def crudeLogUpper (s : ℚ) : ℚ :=
  let t := (1 - s) / (1 + s)
  2 / (1 - s) * (t + t^3 / 3 + t^5 / (5 * (1 - t^2)))

/-- The corrected covered-template statement. It strengthens the original Top
statement only by accepting the additional boundary-corner configurations. -/
def ResponseTypedStatementV2 : Prop :=
  Top.H1Statement →
  (∀ straight : Bool, alphaBound straight ≤ 18094 / 100000 ∧
    betaBound straight ≤ 36751 / 100000 ∧ betaPrimeBound straight ≤ 36751 / 100000) ∧
  ∀ G : Finset Plane, ∀ τ : PinAssignment G, ∀ D : Network G, D.Auxiliary →
    ∀ y : Plane, D.AdmissibleStart y → D.status y = .U →
    ∀ incoming outgoing : Compass, CoveredDepartureV2 D y incoming outgoing →
    let o := y + outgoing.step
    let straight := decide (outgoing = incoming)
    (∀ f : Plane, D.presentNeighbors y = {o, f} → o ≠ f →
      0 < responseBetaPrime D τ y o f ∧
      responseBetaPrime D τ y o f ≤ (betaPrimeBound straight : ℝ) ∧
      responseBetaPrime D τ y o f ≤ reciprocalLogMean (localThreshold straight : ℝ) / 3) ∧
    ∀ f g : Plane, D.presentNeighbors y = {o, f, g} → o ≠ f → o ≠ g → f ≠ g →
      0 < responseAlpha D τ y o f g ∧ responseAlpha D τ y o f g ≤ (alphaBound straight : ℝ) ∧
      0 < responseBeta D τ y o f g ∧ responseBeta D τ y o f g ≤ (betaBound straight : ℝ) ∧
      responseBeta D τ y o f g ≤ reciprocalLogMean ((116 / 125) * (localThreshold straight : ℝ)) / 3 ∧
      responseAlpha D τ y o f g ≤ reciprocalLogMean ((116 / 125) * (localThreshold straight : ℝ)) / 3 -
        reciprocalLogMean (116 / 125) / 5 ∧
      responseI D τ true y o f g ≥ (localThreshold straight : ℝ) * responseJ D τ true y f g ∧
      responseI D τ false y o f g ≥ responseJ D τ false y f g ∧
      responseJ D τ false y f g ≥ 1 ∧ responseJ D τ true y f g ≥ 116 / 125

/-- `l:closure`: erase only the harmless flag pointing at the removed center. -/
def normalizeStart {G : Finset Plane} (D : Network G) (u c : Plane) : Network G :=
  { D with kept := fun x => if x = u ∧ D.status u = .U then (D.kept x).erase c else D.kept x }

/-- A prefix includes its live endpoint, so length zero contains just the start. -/
def prefixNetwork {G : Finset Plane} {n : ℕ} (D : Network G) (u : Plane)
    (w : DirectionWord n) (j : ℕ) : Network G :=
  traceNetwork D ((wordVertices u w).take (j + 1))

/-- `l:onepoint`: exceptions count U departures at arbitrary positions. -/
def uncoveredCount {G : Finset Plane} {n : ℕ} (D : Network G) (u : Plane)
    (incoming : Compass) (w : DirectionWord n) : ℕ := by
  classical
  exact (Finset.univ.filter fun i : Fin n =>
    (prefixNetwork D u w i.val).status (wordVertex u w i.val) = .U ∧
    ¬ CoveredDepartureV2 (prefixNetwork D u w i.val) (wordVertex u w i.val)
      (wordIncoming incoming w i) (w i)).card

/-- A genuinely finite trail sum: distinct original bonds bound the length.
The zero-length class is included and is empty at every admissible start. -/
def stoppedSum {G : Finset Plane} (D : Network G) (u : Plane) (T : Finset Plane)
    (f : (n : ℕ) → DirectionWord n → ℝ) : ℝ :=
  ∑ n ∈ Finset.range (D.bonds.card + 1), ∑ w ∈ stoppedNetworkTrails D u T n, f n w

/-- The common maximum belongs inside the finite sum. -/
def onePointSum {G : Finset Plane} (D : Network G) (τ : PinAssignment G) (u : Plane) : ℝ :=
  stoppedSum D u (protectedSites G) fun _ w =>
    (traceCoefficient D (wordVertices u w) : ℝ) *
      max (traceRatio D τ true (wordVertices u w)) (traceRatio D τ false (wordVertices u w))

/-- Finite distance convention; finiteness at active sites is a separate geometry leaf. -/
def protectedDistance (G : Finset Plane) (x : Plane) : ℕ :=
  (setDistance latticeDist x (↑(protectedSites G) : Set Plane)).toNat

/-- `d:pairenv`: a domain, an ordered pair, its center, and its independent unit pins. -/
structure PairData where
  G : Finset Plane
  τ : PinAssignment G
  D : Network G
  X : PairType
  u : Plane
  v : Plane
  c : Plane
  pair : D.ResponsePair X u v c

/-- Additional data for tracing from the first endpoint; the second need not be interior here. -/
structure PairSetup extends PairData where
  incoming : Compass
  incoming_eq : u = c + incoming.step
  interior : u ∉ protectedSites G

def PairData.normalized (p : PairData) : Network p.G := normalizeStart p.D p.u p.c

def PairData.depth (p : PairData) : ℕ∞ :=
  min (setDistance latticeDist p.u (↑(protectedSites p.G) : Set Plane))
    (setDistance latticeDist p.v (↑(protectedSites p.G) : Set Plane))

def PairData.response (p : PairData) : ℝ :=
  p.D.expectation p.τ true (fun n => dot (n p.u) (n p.v)) -
    p.D.expectation p.τ false (fun n => dot (n p.u) (n p.v))

/-- The target law is unchanged before its first hit. -/
def targetFactor {G : Finset Plane} (D : Network G) (v : Plane) : ℝ :=
  if D.status v = .U then 1 else 3 / 5

/-- The v-terminal summand of the first pair expansion, at one length. -/
def firstLength (p : PairData) (n : ℕ) : ℝ :=
  ∑ w ∈ stoppedNetworkTrails p.normalized p.u (insert p.v (protectedSites p.G)) n,
    if wordVertex p.u w n = p.v then
      (traceCoefficient p.normalized (wordVertices p.u w) : ℝ) *
        (traceRatio p.normalized p.τ true (wordVertices p.u w) -
          traceRatio p.normalized p.τ false (wordVertices p.u w)) * targetFactor p.D p.v
    else 0

/-- `T₁` in §7 lines 756–764. -/
def firstTerm (p : PairData) : ℝ :=
  ∑ n ∈ Finset.range (p.normalized.bonds.card + 1), firstLength p n

/-- `T₂` in §7 lines 756–764. The target is outside S in every use. -/
def secondTerm (p : PairData) : ℝ :=
  stoppedSum p.normalized p.u (insert p.v (protectedSites p.G)) fun n w =>
    if wordVertex p.u w n = p.v then 0 else
      let E := traceNetwork p.normalized (wordVertices p.u w)
      let e := wordVertex p.u w n
      (traceCoefficient p.normalized (wordVertices p.u w) : ℝ) *
        (traceRatio p.normalized p.τ true (wordVertices p.u w) *
            E.expectation p.τ true (fun a => dot (a e) (a p.v)) -
          traceRatio p.normalized p.τ false (wordVertices p.u w) *
            E.expectation p.τ false (fun a => dot (a e) (a p.v)))

def exceptionFactor : ℝ := (12 / 5 : ℝ)^12
def onePointConstant (CV q : ℝ) : ℝ := exceptionFactor * CV / (1 - q)
def sourceConstant (CV q : ℝ) : ℝ := 2 * (12 / 5 : ℝ)^24 * (CV / (1 - q))^2

/-- Real coefficients are used only after finiteness of the ENNReal rows is proved. -/
def realKernel (X Y : PairType) (s : ℕ) : ℝ := (shiftKernel X Y s).toReal

def recursionSeries (X : PairType) (d : ℤ) : ℝ :=
  ∑' j : PairType × ℕ, realKernel X j.1 j.2 * responseEnvelope j.1 (d - (j.2 : ℤ))

/-- One finite length of the shifted matrix, retaining the zero-length zero term. -/
def shiftedLength (θ : ℝ) (X Y : PairType) (n : ℕ) : ℝ≥0∞ :=
  ∑ s ∈ Finset.range (n + 2), ENNReal.ofReal (kernelLengthCoefficient X Y s n : ℝ) *
    ENNReal.ofReal (θ ^ (-(s : ℤ)))

def kernelMajorant (CV q θ : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) * (18094 / 100000 + 2 * (36751 / 100000 : ℝ)) *
    CV * q^n * Real.rpow θ (-(n : ℝ) / 2 - 1)

def witnessReal (X : PairType) : ℝ := (kernelWitness X : ℝ)
def witnessRatio : ℝ := max (witnessReal .B) (witnessReal .C) /
  min (witnessReal .B) (witnessReal .C)

/-- The explicit transport constants in §7 lines 660–676. -/
def transportB (CV q : ℝ) : ℝ :=
  let b := (1 + q) / 2
  let r := q / b
  2 * witnessRatio * (18094 / 100000 + 2 * (36751 / 100000 : ℝ)) * CV *
    b^(-2 : ℤ) * r / (1 - r)^3

def transportEpsilon (CV q : ℝ) : ℝ :=
  min ((1 - (1 + q) / 2) / 2) ((1 - (kernelRho : ℝ)) / (2 * transportB CV q))
def transportTheta (CV q : ℝ) : ℝ := 1 - transportEpsilon CV q
def transportRho : ℝ := (1 + (kernelRho : ℝ)) / 2

/-- A real nonnegative kernel with explicit weighted summability. A real tsum
without this summability premise is insufficient for bounded renewal. -/
def RenewalRows (m : PairType → PairType → ℕ → ℝ) (h : PairType → ℝ)
    (θ ρ : ℝ) : Prop :=
  (∀ X Y s, 0 ≤ m X Y s) ∧ (∀ X, 0 < h X) ∧
  (∀ X, Summable (fun j : PairType × ℕ => m X j.1 j.2 * h j.1 * θ^(-(j.2 : ℤ)))) ∧
  ∀ X, (∑' j : PairType × ℕ, m X j.1 j.2 * h j.1 * θ^(-(j.2 : ℤ))) ≤ ρ * h X

def renewalOp (m : PairType → PairType → ℕ → ℝ)
    (f : PairType → ℤ → ℝ) (X : PairType) (d : ℤ) : ℝ :=
  ∑' j : PairType × ℕ, m X j.1 j.2 * f j.1 (d - (j.2 : ℤ))

def renewalIterate (m : PairType → PairType → ℕ → ℝ)
    (f : PairType → ℤ → ℝ) : ℕ → PairType → ℤ → ℝ
  | 0 => f
  | k + 1 => renewalOp m (renewalIterate m f k)

def renewalSource (CT q : ℝ) (_X : PairType) (d : ℤ) : ℝ :=
  if d ≤ 0 then 2 else CT * q^(2 * d.toNat)

def hmin (h : PairType → ℝ) : ℝ := min (h .B) (h .C)
def hmax (h : PairType → ℝ) : ℝ := max (h .B) (h .C)
def genericAmplitude (h : PairType → ℝ) (CT ρ : ℝ) : ℝ :=
  (hmax h / hmin h) * max 2 CT / (1 - ρ)

end AKLT.Blueprint.Rec
