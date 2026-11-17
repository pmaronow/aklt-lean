module
public import AKLT.Blueprint.Top.Operator
public import AKLT.Blueprint.Top.Response

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

/-! Concrete auxiliary predicates for the Appendix D blueprint. None is a proof
assumption hidden in an instance. In particular, all `...Statement` nodes are
closed; their local premises describe mathematical data, never other nodes. -/

noncomputable section
open scoped BigOperators ComplexOrder
open AKLT.Defs

namespace AKLT.Blueprint.H1

abbrev VectorPolynomial := MvPolynomial (Fin 20 × Fin 3) ℚ
abbrev LocalPolynomial := MvPolynomial LocalVariable ℚ
abbrev TensorSpace (J : Finset (Fin 20)) := EuclideanSpace ℂ (J → Fin 2)

/-- Evaluation before summing internal spins. -/
def localEvaluation (p : LocalPolynomial) (n : Plane → Vec3) (u : Fin 20 → Vec3) : ℝ :=
  MvPolynomial.eval₂ (Rat.castHom ℝ)
    (fun v => match v with | .inl (x, k) => n x k | .inr (j, k) => u j k) p

/-- The finite functional whose rational tensor contraction is `contractSpins`. -/
def rawFunctional (V : Finset Plane) (s : Plane → Status) (p : LocalPolynomial)
    (u : Fin 20 → Vec3) : ℝ :=
  ∑ n : V → SpinLetter, (∏ x : V, spinWeight (s x.val) (n x)) *
    localEvaluation p (supportSpins V n) u

/-- Both support and separate degree are needed for a correct moment contraction. -/
def InternalAdmissible (V : Finset Plane) (p : LocalPolynomial) : Prop :=
  (∀ m ∈ p.support, ∀ x : Plane, x ∉ V → ∀ k : Fin 3, m (.inl (x, k)) = 0) ∧
  ∀ m ∈ p.support, ∀ x : Plane, (∑ k : Fin 3, m (.inl (x, k))) ≤ 4

def LocalVectorAffine (p : LocalPolynomial) : Prop :=
  ∀ m ∈ p.support, ∀ j : Fin 20, (∑ k : Fin 3, m (.inr (j, k))) ≤ 1

def LocalSupportedVectors (J : Finset (Fin 20)) (p : LocalPolynomial) : Prop :=
  ∀ m ∈ p.support, ∀ j : Fin 20, j ∉ J → ∀ k : Fin 3, m (.inr (j, k)) = 0

def IntegrandInvariant (p : LocalPolynomial) : Prop :=
  ∀ R : Matrix (Fin 3) (Fin 3) ℝ, R.transpose * R = 1 →
    ∀ n : Plane → Vec3, ∀ u : Fin 20 → Vec3,
      localEvaluation p (fun x => R.mulVec (n x)) (fun j => R.mulVec (u j)) =
        localEvaluation p n u

def OrthogonalInvariant (p : VectorPolynomial) : Prop :=
  ∀ R : Matrix (Fin 3) (Fin 3) ℝ, R.transpose * R = 1 → ∀ u : Fin 20 → Vec3,
    evaluateReduced p (fun j => R.mulVec (u j)) = evaluateReduced p u

/-- Mathematical inputs extracted from `Top.MomentsStatement`, rather than
assuming any other blueprint leaf. -/
def MonomialMoments : Prop :=
  ∀ m : Fin 3 → ℕ, (∑ i, m i) ≤ 4 → ∀ s : Status, s = .U ∨ s = .D →
    siteFunctional s (fun n => ∏ i, n i ^ m i) = (rationalStatusMoment s m : ℝ)

def ProductMomentCovariance : Prop :=
  ∀ n : ℕ, ∀ s : Fin n → Status, (∀ x, s x = .U ∨ s x = .D) →
    ∀ p : MvPolynomial (Fin n × Fin 3) ℝ, SeparateDegreeFour p →
    ∀ R : Fin n → Matrix (Fin 3) (Fin 3) ℝ, (∀ x, (R x).transpose * R x = 1) →
    productFunctional s (fun a => MvPolynomial.eval (fun v => ((R v.1).mulVec (a v.1)) v.2) p) =
      productFunctional s (fun a => MvPolynomial.eval (fun v => a v.1 v.2) p)

/-- The integrand in the existing `originalPatternPolynomial`, with no new model. -/
def originalIntegrand (π : PatternData) (next : Bool) : LocalPolynomial :=
  (∏ e ∈ π.bonds,
    if next ∧ ({e.1, e.2} : Finset Plane) = {(0, 0), π.outgoing.step} then 1
    else 1 + formalDot (fun k => .inl (e.1, k)) (fun k => .inl (e.2, k))) *
  ∏ j : Fin 20, if π.statusAt (externalSlot j).1 = .X then 1
    else 1 + formalDot (fun k => .inl ((externalSlot j).1, k)) (fun k => .inr (j, k))

def nextStatus (π : PatternData) (next : Bool) (x : Plane) : Status :=
  if next ∧ x = (0, 0) then .D else π.statusAt x

def passageI (o f g : Plane) (n : Plane → Vec3) : ℝ :=
  1 + (dot (n f) (n g) + dot (n f) (n o) + dot (n g) (n o)) / 3

def passageJ (f g : Plane) (n : Plane → Vec3) : ℝ := 1 + dot (n f) (n g) / 5

def PassageNeighbors (π : PatternData) (f g : Plane) : Prop :=
  ({π.outgoing.step, f, g} : Finset Plane) = {(1, 0), (0, 1), (-1, 0)} ∧
    π.outgoing.step ≠ f ∧ π.outgoing.step ≠ g ∧ f ≠ g

/-- The site-level rule, separated from its universal closed Top statement. -/
def LeafRule (π : PatternData) (m : Fin 20 → UnitVector) : Prop :=
  ∀ x ∈ templateCorners ∪ templateTips, π.statusAt x ≠ .X →
    (patternDegree π x = 0 → 0 < siteFunctional (π.statusAt x) (coveredSiteField m x)) ∧
    (patternDegree π x = 1 → ∃ A : ℝ, 0 < A ∧ ∃ u : Vec3, normSq u ≤ 1 ∧
      ∀ v : Vec3, normSq v ≤ 1 →
        siteFunctional (π.statusAt x) (fun n => coveredSiteField m x n * (1 + dot n v)) =
          A * (1 + (replacementRadius π x : ℝ) * dot u v))

def deletedLeafSites (π : PatternData) (r : Representation) : Finset Plane :=
  π.active \ reducedSpinSites π r

def PeripheralGeometry (π : PatternData) (r : Representation) : Prop :=
  ∀ x ∈ deletedLeafSites π r,
    x ∈ templateCorners ∪ templateTips ∧ patternDegree π x ≤ 1 ∧
    (patternDegree π x = 1 → leafNeighbor π x ∈ reducedSpinSites π r) ∧
    ∀ y ∈ deletedLeafSites π r, ¬ Adjacent x y

def integratedLeafFactor (π : PatternData) (m : Fin 20 → UnitVector) (x : Plane)
    (n : Plane → Vec3) : ℝ :=
  siteFunctional (π.statusAt x) (fun z => coveredSiteField m x z *
    (if patternDegree π x = 0 then 1 else 1 + dot z (n (leafNeighbor π x))))

/-- Original factors wholly on the retained spin sites; all deleted-site factors
are accounted for separately by `integratedLeafFactor`. -/
def retainedOriginalFactors (π : PatternData) (r : Representation) (next : Bool)
    (m : Fin 20 → UnitVector) (n : Plane → Vec3) : ℝ :=
  (∏ e ∈ π.bonds, if e.1 ∈ reducedSpinSites π r ∧ e.2 ∈ reducedSpinSites π r ∧
      ¬ (next ∧ ({e.1, e.2} : Finset Plane) = {(0, 0), π.outgoing.step}) then
      1 + dot (n e.1) (n e.2) else 1) *
  ∏ j : Fin 20, if (externalSlot j).1 ∈ reducedSpinSites π r then
    1 + dot (m j).val (n (externalSlot j).1) else 1

def separatedLeafFunctional (π : PatternData) (r : Representation) (next : Bool)
    (m : Fin 20 → UnitVector) : ℝ :=
  let V := reducedSpinSites π r
  ∑ n : V → SpinLetter, (∏ x : V, spinWeight (nextStatus π next x.val) (n x)) *
    retainedOriginalFactors π r next m (supportSpins V n) *
    ∏ x ∈ deletedLeafSites π r, integratedLeafFactor π m x (supportSpins V n)

def UnitChord (v : Vec3) : Prop :=
  ∃ a b : UnitVector, ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ v = t • a.val + (1 - t) • b.val

def SeparatelyAffine (F : (Fin 20 → Vec3) → ℝ) : Prop :=
  ∀ j u a b t, F (Function.update u j (t • a + (1 - t) • b)) =
    t * F (Function.update u j a) + (1 - t) * F (Function.update u j b)

def blochMatrix (u : Vec3) : Matrix (Fin 2) (Fin 2) ℂ :=
  ∑ k : Fin 3, (u k : ℂ) • pauli ⟨k.val + 1, by omega⟩

/-- Real-coefficient companion of the fixed rational Pauli map, used only to
express the intermediate finite spin sum; certificate matrices stay rational. -/
def realPauliOperator (J : Finset (Fin 20)) (p : MvPolynomial (Fin 20 × Fin 3) ℝ) :
    Matrix (J → Fin 2) (J → Fin 2) ℂ :=
  fun σ τ => ∑ a : J → Fin 4,
    (p.coeff (pauliExponent J a) : ℂ) * ∏ j : J, pauli (a j) (σ j) (τ j)

def specializeInternal (p : LocalPolynomial) (n : Plane → Vec3) :
    MvPolynomial (Fin 20 × Fin 3) ℝ :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp (Rat.castHom ℝ))
    (fun v => match v with | .inl (x, k) => MvPolynomial.C (n x k) | .inr v => MvPolynomial.X v) p

def invertRealPolynomial (I : Finset (Fin 20)) (p : MvPolynomial (Fin 20 × Fin 3) ℝ) :
    MvPolynomial (Fin 20 × Fin 3) ℝ :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun v => (if v.1 ∈ I then -1 else 1) * MvPolynomial.X v) p

def rawPauliFunctional (V : Finset Plane) (s : Plane → Status) (J I : Finset (Fin 20))
    (p : LocalPolynomial) : Matrix (J → Fin 2) (J → Fin 2) ℂ :=
  ∑ n : V → SpinLetter, ((∏ x : V, spinWeight (s x.val) (n x) : ℝ) : ℂ) •
    realPauliOperator J (invertRealPolynomial I (specializeInternal p (supportSpins V n)))

def pauliCoordinate (u : Vec3) (a : Fin 4) : ℝ :=
  if h : a.val = 0 then 1 else u ⟨a.val - 1, by omega⟩

def pauliYCount (J : Finset (Fin 20)) (a : J → Fin 4) : ℕ :=
  (Finset.univ.filter fun j => a j = 2).card

def reflectY : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 0, -1, 0; 0, 0, 1]

/-- Equal one-spin factors embedded in two distinct tensor slots. -/
def pairTerm (J : Finset (Fin 20)) (j k : J) (η : ℝ) (n : Vec3) :
    Module.End ℂ (TensorSpace J) :=
  Matrix.toEuclideanLin (tokenMatrix J j (1 + (η : ℂ) • blochMatrix n) *
    tokenMatrix J k (1 + (η : ℂ) • blochMatrix n))

/-- A finite Pauli sum with the chosen pair factored first. Auxiliary factors
commute with its exchange and symmetric projection because their slots are disjoint.
Zero-weight U atoms must be omitted to obtain the unit-spin clause. -/
def PairExpansion (J : Finset (Fin 20)) (j k : J)
    (O : Module.End ℂ (TensorSpace J)) (unitOnly : Prop) : Prop :=
  ∃ t : ℕ, ∃ η : ℝ, η ^ 2 = 1 ∧ ∃ w : Fin t → ℂ, ∃ n : Fin t → Vec3,
    ∃ H : Fin t → Module.End ℂ (TensorSpace J),
      (∀ a, normSq (n a) ≤ 1 ∧ (unitOnly → normSq (n a) = 1)) ∧
      (∀ a, Commute (H a) (exchangeOperator J j k) ∧
        Commute (H a) (symmetricPairProjection J j k)) ∧
      O = ∑ a, w a • (pairTerm J j k η (n a) * H a)

def sectorVector (π : PatternData) (r : Representation) (ε : ExchangeSigns π)
    (b : ExchangeBasis π r ε) : TensorSpace (reductionVectors π r) :=
  WithLp.toLp 2 (fun σ => (exchangeBasisVector π r ε b σ : ℂ))

def SpinStable (J : Finset (Fin 20)) (S : Submodule ℂ (TensorSpace J)) : Prop :=
  (∀ ψ ∈ S, totalSpinZ J ψ ∈ S) ∧
  (∀ ψ ∈ S, totalSpinPlus J ψ ∈ S) ∧ ∀ ψ ∈ S, totalSpinMinus J ψ ∈ S

def WeightLadder (J : Finset (Fin 20)) : Prop :=
  ∀ v : TensorSpace J, ∀ m : ℝ, totalSpinZ J v = (m : ℂ) • v →
    (totalSpinZ J (totalSpinPlus J v) = ((m + 1 : ℝ) : ℂ) • totalSpinPlus J v) ∧
    (totalSpinZ J (totalSpinMinus J v) = ((m - 1 : ℝ) : ℂ) • totalSpinMinus J v) ∧
    (v ≠ 0 → 0 < m → totalSpinMinus J v ≠ 0) ∧
    (v ≠ 0 → m < 0 → totalSpinPlus J v ≠ 0)

/-- Exact data expected from the finite-certificate owner. This is the existing
Top certificate premise, factored into a reusable data predicate. -/
def SectorWitnesses (π : PatternData) (r : Representation) (I : Finset (Fin 20))
    (D₀ p q : ℕ) : Prop :=
  ∀ ε : ExchangeSigns π, ∃ t : ℕ, ∃ index : Fin t ≃ CentralBasis π r ε,
    ∃ g d S : ℕ, ∃ L : Matrix (Fin t) (Fin t) ℤ,
      (∀ i j, i < j → L i j = 0) ∧
      GramResidualRows (indexedSectorMatrix π r ε I D₀ p q index) L g d S

def h1Numerator (π : PatternData) : ℕ := if π.outgoing = .north then 961 else 187
def h1Denominator (π : PatternData) : ℕ := if π.outgoing = .north then 1000 else 200

end AKLT.Blueprint.H1
