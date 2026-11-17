module
public import AKLT.Blueprint.Rec.NodesLocal

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.Blueprint.Rec

/-- `l:stepid`, §6 lines 100–142. Expand at most three factors and use
only first through fourth moments. Empty sums are zero. -/
def UStepMomentStatement : Prop :=
  ∀ k : ℕ, k ≤ 3 → ∀ a : Vec3, ∀ u : Fin k → Vec3,
    siteFunctional .U (fun n => dot a n * ∏ i, (1 + dot n (u i))) =
      (1 / 3 : ℝ) * ∑ i, dot a (u i) *
        siteFunctional .D (fun n => ∏ j ∈ Finset.univ.erase i, (1 + dot n (u j)))

/-- `l:stepid`, §6 lines 143–146. Only k≤1 is allowed for D; in
particular this statement never expands an initial two-bond D site. -/
def DStepMomentStatement : Prop :=
  ∀ k : ℕ, k ≤ 1 → ∀ a : Vec3, ∀ u : Fin k → Vec3,
    siteFunctional .D (fun n => dot a n * ∏ i, (1 + dot n (u i))) =
      (1 / 5 : ℝ) * ∑ i, dot a (u i)

/-- `d:trace`, §6 lines 71–91. An unused initial bond remains present
at the corresponding prefix. Departures are admissible and each prefix
is auxiliary; no departure is from the original protected layer. -/
def TraceDynamicsStatement : Prop :=
  ∀ G : Finset Plane, ∀ D : Network G, D.Auxiliary → ∀ u : Plane,
    D.AdmissibleStart u → ∀ T : Finset Plane, ∀ n : ℕ, ∀ w : DirectionWord n,
    StoppedNetworkTrail D u T w →
    (∀ j ≤ n, (prefixNetwork D u w j).Auxiliary) ∧
    ∀ i : Fin n,
      (prefixNetwork D u w i.val).AdmissibleStart (wordVertex u w i.val) ∧
      (prefixNetwork D u w i.val).Present (wordVertex u w i.val) (wordVertex u w (i.val + 1))

/-- `d:trace`, §6 lines 90–98. The coefficient is positive and exactly
3^-n(3/5)^N_D. Count statuses at evolving departures, not initial statuses. -/
def TraceCoefficientStatement : Prop :=
  ∀ G : Finset Plane, ∀ D : Network G, D.Auxiliary → ∀ u : Plane,
    D.AdmissibleStart u → ∀ T : Finset Plane, ∀ n : ℕ, ∀ w : DirectionWord n,
    StoppedNetworkTrail D u T w →
    let ND := (Finset.univ.filter fun i : Fin n =>
      (prefixNetwork D u w i.val).status (wordVertex u w i.val) = .D).card
    0 < traceCoefficient D (wordVertices u w) ∧
      traceCoefficient D (wordVertices u w) = (1 / 3 : ℚ)^n * (3 / 5 : ℚ)^ND

/-- `d:trace`, §6 lines 95–98. Telescope strictly positive normalizers;
the zero-length product is one. -/
def TraceTelescopeStatement : Prop :=
  ∀ G : Finset Plane, ∀ τ : PinAssignment G, ∀ D : Network G, D.Auxiliary →
    ∀ u : Plane, D.AdmissibleStart u → ∀ T : Finset Plane, ∀ n : ℕ,
    ∀ w : DirectionWord n, StoppedNetworkTrail D u T w → ∀ b : Bool,
    traceRatio D τ b (wordVertices u w) =
      ∏ i : Fin n, stepRatio (prefixNetwork D u w i.val) τ b
        (wordVertex u w i.val) (wordVertex u w (i.val + 1))

/-- `p:pairwalk`, §6 lines 166–194. Apply the site moment identity to
one moving coordinate. The target has the stated incident-factor bound. -/
def CoordinateStepStatement : Prop :=
  ∀ G : Finset Plane, ∀ τ : PinAssignment G, ∀ D : Network G, D.Auxiliary →
    ∀ u v : Plane, D.AdmissibleStart u → AdmissibleTarget D v → u ≠ v →
    ∀ b : Bool, ∀ k : Fin 3,
      D.partition τ b (fun a => a u k * a v k) =
        (if D.status u = .U then (1 / 3 : ℝ) else 1 / 5) *
          ∑ o ∈ D.presentNeighbours u,
            (traceStep D u o).partition τ b (fun a => a o k * a v k)

/-- `p:pairwalk`, §6 lines 196–212. Induct on the finite set of unused
bonds. Dead branches give an empty sum; length is at most D.bonds.card. -/
def PairExpansionStatement : Prop :=
  ∀ G : Finset Plane, ∀ τ : PinAssignment G, ∀ D : Network G, D.Auxiliary →
    ∀ u v : Plane, D.AdmissibleStart u → AdmissibleTarget D v → u ≠ v → ∀ b : Bool,
      D.expectation τ b (fun a => dot (a u) (a v)) =
        stoppedSum D u (insert v (protectedSites G)) fun n w =>
          (traceCoefficient D (wordVertices u w) : ℝ) * traceRatio D τ b (wordVertices u w) *
            (traceNetwork D (wordVertices u w)).expectation τ b
              (fun a => dot (a (wordVertex u w n)) (a v))

/-- `p:pairwalk`, §6 lines 214–222. At the first hit of the target its
law is unchanged; a U target has norm one and a D target is now isolated. -/
def PairTerminalFactorStatement : Prop :=
  ∀ G : Finset Plane, ∀ τ : PinAssignment G, ∀ D : Network G, D.Auxiliary →
    ∀ u v : Plane, D.AdmissibleStart u → AdmissibleTarget D v → u ≠ v →
    ∀ n : ℕ, ∀ w : DirectionWord n,
    StoppedNetworkTrail D u (insert v (protectedSites G)) w →
    wordVertex u w n = v → ∀ b : Bool,
      (traceNetwork D (wordVertices u w)).expectation τ b (fun a => normSq (a v)) =
        targetFactor D v

/-- Factor count, including the original leg factors that survive the trace. -/
def factorDegree {G : Finset Plane} (D : Network G) (x : Plane) : ℕ :=
  (D.presentNeighbours x).card + ((originalLegs G).filter fun e => e.1 = x).card

/-- `p:pairwalk`, §6 lines 224–237. Every numerator in the iteration
has separate degree≤4. In particular a terminal protected endpoint has
lost its arrival bond before the insertion, and a self-pair adds degree two. -/
def PairDegreeStatement : Prop :=
  ∀ G : Finset Plane, ∀ D : Network G, D.Auxiliary → ∀ u v : Plane,
    D.AdmissibleStart u → AdmissibleTarget D v → u ≠ v →
    ∀ n : ℕ, ∀ w : DirectionWord n,
    StoppedNetworkTrail D u (insert v (protectedSites G)) w →
    ∀ j ≤ n, ∀ x ∈ (prefixNetwork D u w j).active,
      factorDegree (prefixNetwork D u w j) x +
        (if x = wordVertex u w j then 1 else 0) + (if x = v then 1 else 0) ≤ 4

/-- `l:exposure`, §6 lines 452–485. Telescoping products in an arbitrary
enumeration of U departures. The empty index type gives 0≤0. -/
def ProductExposureStatement : Prop :=
  ∀ n : ℕ, ∀ b c x : Fin n → ℝ,
    (∀ i, 0 < b i ∧ 0 < c i ∧ c i ≤ 1 ∧ b i ≤ x i ∧ 1 ≤ x i) →
    |(∏ i, b i) - ∏ i, c i| ≤
      ∑ i, |Real.log (c i) - Real.log (b i)| *
        ∏ j ∈ Finset.univ.filter (fun j : Fin n => j.val ≤ i.val), x j

/-- `l:onepoint`, §6 lines 711–753. Compare each step, take the same
majorant for both pin choices, and only then take their maximum. -/
def OnePointPointwiseStatement : Prop :=
  Top.H1Statement → ∀ G : Finset Plane, ∀ τ : PinAssignment G, ∀ D : Network G,
    D.Auxiliary → ∀ u : Plane, D.AdmissibleStart u → ∀ incoming : Compass,
    ¬ D.Present (u - incoming.step) u → ∀ n : ℕ, ∀ w : DirectionWord n,
    StoppedNetworkTrail D u (protectedSites G) w → uncoveredCount D u incoming w ≤ 12 →
      (traceCoefficient D (wordVertices u w) : ℝ) *
        max (traceRatio D τ true (wordVertices u w)) (traceRatio D τ false (wordVertices u w)) ≤
          exceptionFactor * (trailWeight u incoming w : ℝ)

/-- `l:onepoint`, §6 lines 755–775. Group by length, enlarge to the H2
class with the same incoming direction, and sum a geometric tail.
The distance is to original S; it is finite at the admissible start. -/
def OnePointSumStatement : Prop :=
  Top.H1Statement → ∀ CV q : ℝ, OpenTrailBound CV q →
    ∀ G : Finset Plane, ∀ τ : PinAssignment G, ∀ D : Network G, D.Auxiliary →
    ∀ u : Plane, D.AdmissibleStart u → ∀ incoming : Compass,
    ¬ D.Present (u - incoming.step) u →
    (∀ n : ℕ, ∀ w : DirectionWord n, StoppedNetworkTrail D u (protectedSites G) w →
      uncoveredCount D u incoming w ≤ 12) →
    onePointSum D τ u ≤ onePointConstant CV q * q^(protectedDistance G u)

/-- Length-zero coefficients are normalized, with no scalar trace mass. -/
theorem traceCoefficient_singleton {G : Finset Plane} (D : Network G) (u : Plane) :
    traceCoefficient D [u] = 1 := rfl

end AKLT.Blueprint.Rec
