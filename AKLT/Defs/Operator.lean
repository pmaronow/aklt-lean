module
public import AKLT.Defs.Pattern
public import AKLT.Defs.Frame

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators

namespace AKLT.Defs

/-- `d:reduction`: exactly the two permitted leaf representations. -/
inductive Representation where
  | reduced | unreduced
  deriving DecidableEq, Repr

instance : Fintype Representation := ⟨{.reduced, .unreduced}, by intro r; cases r <;> simp⟩

/-- Internal template degree before passage integration. -/
def patternDegree (π : PatternData) (x : Plane) : ℕ :=
  (π.bonds.filter fun e => e.1 = x ∨ e.2 = x).card

/-- `d:reduction`: a tip or corner has a single replacement precisely in these cases. -/
def SingleReplacement (π : PatternData) (r : Representation) (x : Plane) : Prop :=
  patternDegree π x = 1 ∧ (x ∈ templateTips ∨ (r = .reduced ∧ x ∈ templateCorners))

/-- `d:reduction`: retained spin sites; deleted positive leaf factors are omitted in both polynomials. -/
def reducedSpinSites (π : PatternData) (r : Representation) : Finset Plane := by
  classical
  exact π.active.filter fun x => x ∉ templateTips ∧
    (x ∉ templateCorners ∨ (patternDegree π x ≠ 0 ∧ ¬ SingleReplacement π r x))

/-- The eight possible vector groups are indexed by their original corner or tip. -/
def reductionGroups (π : PatternData) : Finset Plane :=
  (templateCorners ∪ templateTips).filter fun x => 0 < patternDegree π x

/-- First original external-slot index at a group. -/
def groupLeader (x : Plane) : Fin 20 :=
  if x = (1, 1) then 0 else if x = (-1, 1) then 2 else
  if x = (-1, -1) then 4 else if x = (1, -1) then 6 else
  if x = (2, 0) then 8 else if x = (0, 2) then 11 else if x = (-2, 0) then 14 else 17

/-- Second slot of a retained corner; the totalized value is unused for singles. -/
def groupSecond (x : Plane) : Fin 20 := ⟨min 19 ((groupLeader x).val + 1), by omega⟩

/-- `d:reduction`: a group is a single or one retained two-slot corner. -/
def groupIsPair (π : PatternData) (r : Representation) (x : Plane) : Bool := by
  classical
  exact decide (x ∈ templateCorners ∧ ¬ SingleReplacement π r x)

/-- `d:reduction`: active vector tokens; unused original slot variables are absent. -/
def reductionVectors (π : PatternData) (r : Representation) : Finset (Fin 20) :=
  (reductionGroups π).biUnion fun x =>
    if groupIsPair π r x then {groupLeader x, groupSecond x} else {groupLeader x}

/-- `d:reduction`: the exact replacement radii. -/
def replacementRadius (π : PatternData) (x : Plane) : ℚ :=
  if x ∈ templateTips then 3 / 5 else if π.statusAt x = .U then 1 / 2 else 1 / 3

/-- The unique internal neighbour of a singly bonded leaf, with a harmless totalization. -/
def leafNeighbour (π : PatternData) (x : Plane) : Plane :=
  ((π.bonds.toList.filterMap fun e =>
    if e.1 = x then some e.2 else if e.2 = x then some e.1 else none).headD (0, 0))

/-- Formal variables are internal spin coordinates or remaining vector coordinates. -/
abbrev LocalVariable := (Plane × Fin 3) ⊕ (Fin 20 × Fin 3)

/-- A formal scalar product in a rational polynomial ring. -/
def formalDot {σ : Type*} (a b : Fin 3 → σ) : MvPolynomial σ ℚ :=
  ∑ k : Fin 3, MvPolynomial.X (a k) * MvPolynomial.X (b k)

/-- `l:moments`: exact rational degree-four monomial tensor, without real radicals in certificates. -/
def rationalMoment (m : Fin 3 → ℕ) : ℚ :=
  if (∑ i, m i) = 0 then 1 else
  if (∑ i, m i) = 2 ∧ ∃ i, m i = 2 then 1 / 3 else
  if (∑ i, m i) = 4 ∧ ∃ i, m i = 4 then 1 / 5 else
  if (∑ i, m i) = 4 ∧ (∀ i, Even (m i)) then 1 / 15 else 0

/-- `d:moment`: D has unit constant moment and 3/5 of each positive-degree tensor. -/
def rationalStatusMoment (s : Status) (m : Fin 3 → ℕ) : ℚ :=
  if s = .D ∧ (∑ i, m i) ≠ 0 then (3 / 5) * rationalMoment m else rationalMoment m

/-- Finite moment contraction of the internal spin variables, retaining the vector monomials. -/
def contractSpins (V : Finset Plane) (status : Plane → Status)
    (p : MvPolynomial LocalVariable ℚ) : MvPolynomial (Fin 20 × Fin 3) ℚ :=
  ∑ m ∈ p.support,
    MvPolynomial.monomial (Finsupp.comapDomain Sum.inr m (by
      intro a _ b _ h
      exact Sum.inr.inj h))
      (p.coeff m * ∏ x ∈ V, rationalStatusMoment (status x) (fun k => m (.inl (x, k))))

/-- `d:reduction`: actual rational polynomial before internal moment contraction.
Singleton factors use the exact leaf radii; retained corners keep both original slots. -/
def reducedIntegrand (π : PatternData) (r : Representation) (next : Bool) :
    MvPolynomial LocalVariable ℚ :=
  let V := reducedSpinSites π r
  (∏ e ∈ π.bonds,
    if e.1 ∈ V ∧ e.2 ∈ V ∧
      ¬ (next ∧ ({e.1, e.2} : Finset Plane) = {(0, 0), π.outgoing.step}) then
      1 + formalDot (fun k => .inl (e.1, k)) (fun k => .inl (e.2, k)) else 1) *
  (∏ x ∈ reductionGroups π,
    if groupIsPair π r x then
      (1 + formalDot (fun k => .inl (x, k)) (fun k => .inr (groupLeader x, k))) *
      (1 + formalDot (fun k => .inl (x, k)) (fun k => .inr (groupSecond x, k)))
    else 1 + MvPolynomial.C (replacementRadius π x) *
      formalDot (fun k => .inl (leafNeighbour π x, k)) (fun k => .inr (groupLeader x, k)))

/-- `d:reduction`: the reconstructed current and next polynomials, not supplied certificate matrices. -/
def reducedPolynomial (π : PatternData) (r : Representation) (next : Bool) :
    MvPolynomial (Fin 20 × Fin 3) ℚ :=
  contractSpins (reducedSpinSites π r)
    (fun x => if next ∧ x = (0, 0) then .D else π.statusAt x) (reducedIntegrand π r next)

/-- `d:reduction`: the difference polynomial at an exact rational threshold. -/
def reducedDifference (π : PatternData) (r : Representation) (c : ℚ) :
    MvPolynomial (Fin 20 × Fin 3) ℚ :=
  reducedPolynomial π r false - MvPolynomial.C c * reducedPolynomial π r true

/-- `d:Pauli`: affine in each entire vector, rather than separately in each scalar coordinate. -/
def VectorAffine (p : MvPolynomial (Fin 20 × Fin 3) ℚ) : Prop :=
  ∀ m ∈ p.support, ∀ j : Fin 20, (∑ k : Fin 3, m (j, k)) ≤ 1

/-- `d:Pauli`: inversion of selected vector tokens. -/
def invertPolynomial (I : Finset (Fin 20)) (p : MvPolynomial (Fin 20 × Fin 3) ℚ) :
    MvPolynomial (Fin 20 × Fin 3) ℚ :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun v =>
    (if v.1 ∈ I then -1 else 1) * MvPolynomial.X v) p

/-- `d:reduction`: an allowed inversion is a union of whole groups. -/
def GroupInversion (π : PatternData) (r : Representation) (I : Finset (Fin 20)) : Prop :=
  I ⊆ reductionVectors π r ∧ ∀ x ∈ reductionGroups π, groupIsPair π r x = true →
    (groupLeader x ∈ I ↔ groupSecond x ∈ I)

/-- Monomial exponent for the unique vector-affine Pauli expansion. -/
def pauliExponent (J : Finset (Fin 20)) (a : J → Fin 4) : (Fin 20 × Fin 3) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun v =>
    if h : v.1 ∈ J then if (a ⟨v.1, h⟩).val = v.2.val + 1 then 1 else 0 else 0

/-- `d:Pauli`: concrete tensor-basis operator, with no tensor-product library choices. -/
def pauliOperator (J : Finset (Fin 20)) (p : MvPolynomial (Fin 20 × Fin 3) ℚ) :
    Matrix (J → Fin 2) (J → Fin 2) ℂ :=
  fun σ τ => ∑ a : J → Fin 4,
    (p.coeff (pauliExponent J a) : ℂ) * ∏ j : J, pauli (a j) (σ j) (τ j)

/-- Rational complex arithmetic used for exact sector reconstruction. -/
def ratComplexMul (a b : ℚ × ℚ) : ℚ × ℚ := (a.1 * b.1 - a.2 * b.2, a.1 * b.2 + a.2 * b.1)

/-- Rational real/imaginary Pauli entries. -/
def rationalPauli (a : Fin 4) (i j : Fin 2) : ℚ × ℚ :=
  if a = 0 then (if i = j then 1 else 0, 0) else
  if a = 1 then (if i ≠ j then 1 else 0, 0) else
  if a = 2 then (0, if i = j then 0 else if i = 0 then -1 else 1) else
    (if i ≠ j then 0 else if i = 0 then 1 else -1, 0)

/-- Exact rational real part of the operator entry, reconstructed from polynomial coefficients. -/
def rationalOperatorEntry (J : Finset (Fin 20)) (p : MvPolynomial (Fin 20 × Fin 3) ℚ)
    (σ τ : J → Fin 2) : ℚ :=
  ∑ a : J → Fin 4, p.coeff (pauliExponent J a) *
    (((Finset.univ : Finset J).toList.map fun j => rationalPauli (a j) (σ j) (τ j)).foldl
      ratComplexMul (1, 0)).1

/-- `d:exchange`: one sign for each retained D pair; unused signs are immaterial. -/
abbrev ExchangeSigns (π : PatternData) := reductionGroups π → Bool

/-- The actual type of a group basis: two singles, three symmetric, or one exterior vector. -/
def GroupBasis (π : PatternData) (r : Representation) (ε : ExchangeSigns π)
    (x : reductionGroups π) : Type :=
  Fin (if groupIsPair π r x.val then if π.statusAt x.val = .D ∧ ε x = false then 1 else 3 else 2)

instance (π : PatternData) (r : Representation) (ε : ExchangeSigns π) (x : reductionGroups π) :
    Fintype (GroupBasis π r ε x) := inferInstanceAs (Fintype (Fin _))

/-- `d:exchange`: the integer-coordinate tensor-sector basis. -/
abbrev ExchangeBasis (π : PatternData) (r : Representation) (ε : ExchangeSigns π) :=
  (x : reductionGroups π) → GroupBasis π r ε x

/-- Magnetic weight of an integer-coordinate sector vector. -/
def exchangeWeight (π : PatternData) (r : Representation) (ε : ExchangeSigns π)
    (b : ExchangeBasis π r ε) : ℚ :=
  ∑ x : reductionGroups π,
    if groupIsPair π r x.val then
      if π.statusAt x.val = .D ∧ ε x = false then 0 else 1 - ((b x).val : ℚ)
    else 1 / 2 - ((b x).val : ℚ)

/-- `d:exchange`: central weight is determined by the number of singles. -/
def centralWeight (π : PatternData) (r : Representation) : ℚ :=
  if Even ((reductionGroups π).filter fun x => !groupIsPair π r x).card then 0 else 1 / 2

/-- `d:exchange`: actual central-weight basis, with its unnormalized integer coordinates. -/
abbrev CentralBasis (π : PatternData) (r : Representation) (ε : ExchangeSigns π) :=
  {b : ExchangeBasis π r ε // exchangeWeight π r ε b = centralWeight π r}

noncomputable instance (π : PatternData) (r : Representation) (ε : ExchangeSigns π) :
    Fintype (CentralBasis π r ε) := by
  classical
  exact Fintype.ofFinite _

/-- Integer coefficients of each supported exchange-sector basis vector in the full tensor basis. -/
def exchangeBasisVector (π : PatternData) (r : Representation) (ε : ExchangeSigns π)
    (b : ExchangeBasis π r ε) (σ : reductionVectors π r → Fin 2) : ℤ :=
  ∏ x : reductionGroups π,
    let i := σ ⟨groupLeader x.val, by
      apply Finset.mem_biUnion.mpr; refine ⟨x.val, x.property, ?_⟩
      split <;> simp⟩
    if h : groupIsPair π r x.val = true then
      let j := σ ⟨groupSecond x.val, by
        apply Finset.mem_biUnion.mpr; exact ⟨x.val, x.property, by simp [h]⟩⟩
      if π.statusAt x.val = .D ∧ ε x = false then
        if i = 0 ∧ j = 1 then 1 else if i = 1 ∧ j = 0 then -1 else 0
      else if (b x).val = 0 then if i = 0 ∧ j = 0 then 1 else 0
      else if (b x).val = 1 then if i ≠ j then 1 else 0
      else if i = 1 ∧ j = 1 then 1 else 0
    else if i.val = (b x).val then 1 else 0

/-- Exact rational Hermitian-form entry in the unnormalized central-sector basis. -/
def rationalSectorEntry (π : PatternData) (r : Representation) (ε : ExchangeSigns π)
    (p : MvPolynomial (Fin 20 × Fin 3) ℚ) (a b : CentralBasis π r ε) : ℚ :=
  ∑ σ, ∑ τ, (exchangeBasisVector π r ε a.val σ : ℚ) *
    rationalOperatorEntry (reductionVectors π r) p σ τ * (exchangeBasisVector π r ε b.val τ : ℚ)

/-- `l:integercheck`: a justified denominator clears 3D0 current and 5D0 next coefficients. -/
def ClearsDenominator (π : PatternData) (r : Representation) (D₀ : ℕ) : Prop :=
  0 < D₀ ∧ ∀ next : Bool, ∀ m ∈ (reducedPolynomial π r next).support,
    ∃ z : ℤ, ((if next then 5 else 3) * (D₀ : ℚ) * (reducedPolynomial π r next).coeff m) = z

/-- `l:integercheck`: reconstructed integer A or A', never an arbitrary stored matrix. -/
def integerSectorMatrix (π : PatternData) (r : Representation) (ε : ExchangeSigns π)
    (I : Finset (Fin 20)) (D₀ : ℕ) (next : Bool) :
    Matrix (CentralBasis π r ε) (CentralBasis π r ε) ℤ :=
  fun a b => ⌊(if next then 5 else 3) * (D₀ : ℚ) * rationalSectorEntry π r ε
    (invertPolynomial I (reducedPolynomial π r next)) a b⌋

/-- `l:integercheck`: the exact threshold sector matrix 5q A - 3p A'. -/
def thresholdSectorMatrix (π : PatternData) (r : Representation) (ε : ExchangeSigns π)
    (I : Finset (Fin 20)) (D₀ p q : ℕ) :
    Matrix (CentralBasis π r ε) (CentralBasis π r ε) ℤ :=
  (5 * (q : ℤ)) • integerSectorMatrix π r ε I D₀ false -
    (3 * (p : ℤ)) • integerSectorMatrix π r ε I D₀ true

/-- `l:gram-residual`: residual with independent positive integer scales. -/
def gramResidual {ι : Type*} [Fintype ι] (M L : Matrix ι ι ℤ) (g d S : ℕ) : Matrix ι ι ℤ :=
  ((d : ℤ) * (S : ℤ)^2) • M - (g : ℤ) • (L * L.transpose)

/-- `l:gram-residual`: exact division-free row conditions, including positive diagonal. -/
def GramResidualRows {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M L : Matrix ι ι ℤ) (g d S : ℕ) : Prop :=
  0 < g ∧ 0 < d ∧ 0 < S ∧
  ∀ i, 0 < gramResidual M L g d S i i ∧
    (∑ j ∈ Finset.univ.erase i, |gramResidual M L g d S i j|) < gramResidual M L g d S i i

end AKLT.Defs
