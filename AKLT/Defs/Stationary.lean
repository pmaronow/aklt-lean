module
public import AKLT.Defs.Automaton

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
set_option maxRecDepth 2048

namespace AKLT.Defs

/-- `d:phaseweights`: four phases, unrelated to the pair types B and C. -/
inductive Phase where
  | A | B | C | D
  deriving DecidableEq, Repr

instance : Fintype Phase := ⟨{.A, .B, .C, .D}, by intro φ; cases φ <;> simp⟩

/-- `d:phaseweights`: terminal rewards 0,0,1,1. -/
def phaseTerminal : Phase → ℚ | .A => 0 | .B => 0 | .C => 1 | .D => 1

/-- `d:phaseweights`: one unit in A and B initially. -/
def phaseInitial : Phase → ℚ | .A => 1 | .B => 1 | .C => 0 | .D => 0

/-- `d:phaseweights`: the four diagonal rows, with weight 1/5 at a revisit. -/
def phaseDiagonal (φ : Phase) (k : StepKind) : ℚ :=
  if k = .revisit then 1 / 5 else
    match φ, k with
    | .A, .straight | .B, .straight | .C, .straight => passageFactor true / 3
    | .A, .turn => passageFactor false / 3
    | _, _ => 1 / 3

/-- `d:phaseweights`: the only two allowed changes of phase. -/
def phaseTransition (k : StepKind) (reward : ℚ) (φ ψ : Phase) : ℚ :=
  if φ = ψ then phaseDiagonal φ k else
    if φ = .A ∧ ψ = .C ∧ k = .turn then passageFactor false * reward / 3 else
    if φ = .B ∧ ψ = .D ∧ k = .straight then passageFactor true * reward / 3 else 0

/-- Type-dependent h reward when a chosen set of neighbours is declared dead. -/
def relaxedReward (x : Plane) (incoming outgoing : Compass) (dead : Finset Plane) : ℚ :=
  let o := x + outgoing.step
  let live := ((neighbours x).erase (x - incoming.step) |>.erase o) \ dead
  ∑ p ∈ (insert o live).powersetCard 2,
    (if o ∈ p then
      if live.card = 1 then betaPrimeBound (decide (outgoing = incoming))
      else betaBound (decide (outgoing = incoming))
    else alphaBound (decide (outgoing = incoming))) * kernelWitness (responsePairType p)

/-- `d:stationary-walk`: free operator without spatial or known-site rules. -/
def freeCoefficient {m q : ℕ} (Q : MemoryQuotient m q)
    (φ : Phase) (a : Fin q) (d : Compass) (ψ : Phase) : ℚ :=
  if Q.allowed a d then phaseTransition (Q.kind a d)
    (relaxedReward (0, 0) (Q.arrival a) d ∅) φ ψ else 0

/-- Legacy stationary coefficients, retained for existing H3 proofs.
Use `stationaryCoefficientV2` for the paper's zero-centre-edge operator. -/
def stationaryCoefficient {m q : ℕ} (Q : MemoryQuotient m q) (X : PairType) (d₀ : Compass)
    (φ : Phase) (a : Fin q) (x : Plane) (d : Compass) (ψ : Phase) : ℚ :=
  if x = kernelCentre ∨ x = kernelTarget X ∨ Q.allowed a d = false then 0 else
    if x = kernelStart ∨ x = kernelStart + d₀.step then
      if ({x, x + d.step} : Finset Plane) = {kernelStart, kernelStart + d₀.step} ∨
        Q.kind a d = .revisit then 0 else if φ = ψ then 1 / 5 else 0
    else if x + d.step = kernelCentre then 0 else
      phaseTransition (Q.kind a d)
        (relaxedReward x (Q.arrival a) d {kernelCentre}) φ ψ

/-- Legacy backward operator, retained for existing H3 proofs.
The corrected arbitrary-function operator is `stationaryApplyV2`. -/
def stationaryApply {m q : ℕ} (Q : MemoryQuotient m q) (X : PairType) (d₀ : Compass)
    (F : Phase → Fin q → Plane → ℚ) (φ : Phase) (a : Fin q) (x : Plane) : ℚ :=
  ∑ d : Compass, ∑ ψ : Phase,
    stationaryCoefficient Q X d₀ φ a x d ψ * F ψ (Q.successor a d) (x + d.step)

/-- `d:stationary-walk`: the position-free backward operator W. -/
def freeApply {m q : ℕ} (Q : MemoryQuotient m q) (z : Phase → Fin q → ℚ)
    (φ : Phase) (a : Fin q) : ℚ :=
  ∑ d : Compass, ∑ ψ : Phase, freeCoefficient Q φ a d ψ * z ψ (Q.successor a d)

/-- `d:stationary-certificate`: the frozen spatial radius. -/
def certificateRadius : ℕ := 70

/-- The value scale, separate from the coefficient scale. -/
def certificateValueScale : ℕ := 2 ^ 16

/-- The independently rounded coefficient scale. -/
def certificateCoefficientScale : ℕ := 2 ^ 48

/-- Exact rational coefficient ceiling, never a floating point diagnostic. -/
def coefficientCeiling (t : ℚ) : ℕ := ⌈(certificateCoefficientScale : ℚ) * t⌉₊

/-- `d:stationary-certificate`: finite integer arrays; passing their checks is a separate Prop. -/
structure StationaryData (q : ℕ) where
  cap : Phase → Fin q → ℕ
  value : Phase → Fin q → square (0, 0) certificateRadius → ℕ

/-- The global extension is capped outside the finite square, without spatial periodicity. -/
def StationaryData.extended {q : ℕ} (C : StationaryData q)
    (φ : Phase) (a : Fin q) (x : Plane) : ℕ := by
  classical
  exact if h : x ∈ square (0, 0) certificateRadius then C.value φ a ⟨x, h⟩ else C.cap φ a

/-- `d:stationary-certificate`: the finite-valued rational potential on all lattice sites. -/
def StationaryData.potential {q : ℕ} (C : StationaryData q)
    (φ : Phase) (a : Fin q) (x : Plane) : ℚ :=
  (C.extended φ a x : ℚ) / certificateValueScale

/-- `d:stationary-certificate`: all integer free rows, caps, terminal values and local rows. -/
def StationaryData.Passes {m q : ℕ} (C : StationaryData q) (Q : MemoryQuotient m q)
    (X : PairType) (d₀ : Compass) : Prop :=
  (∀ φ a, 0 < C.cap φ a) ∧
  (∀ a, certificateValueScale ≤ C.cap .C a ∧ certificateValueScale ≤ C.cap .D a) ∧
  (∀ φ a, (∑ d : Compass, ∑ ψ : Phase,
    coefficientCeiling (freeCoefficient Q φ a d ψ) * C.cap ψ (Q.successor a d)) ≤
      certificateCoefficientScale * C.cap φ a) ∧
  (∀ φ a x, C.value φ a x ≤ C.cap φ a) ∧
  (∀ φ a, C.extended φ a kernelCentre = 0 ∧
    (C.extended φ a (kernelTarget X) : ℚ) = certificateValueScale * phaseTerminal φ) ∧
  ∀ φ a (x : square (0, 0) certificateRadius),
    x.val ≠ kernelCentre → x.val ≠ kernelTarget X →
    (∑ d : Compass, ∑ ψ : Phase,
      coefficientCeiling (stationaryCoefficient Q X d₀ φ a x.val d ψ) *
        C.extended ψ (Q.successor a d) (x.val + d.step)) ≤
      certificateCoefficientScale * C.value φ a x

/-- Actual phase weights along a true prefix, with its true revisits and dead neighbours. -/
def prefixPhases {n : ℕ} (w : DirectionWord n) : Phase → ℚ :=
  (List.finRange n).foldl (fun p i ψ => ∑ φ : Phase, p φ *
    phaseTransition (if wordRevisit kernelStart w i then .revisit
      else if wordStraight kernelIncoming w i then .straight else .turn) (witnessKappa w i) φ ψ)
    phaseInitial

/-- A first direction, also total for an empty word (where it is false). -/
def FirstDirection {n : ℕ} (w : DirectionWord n) (d : Compass) : Prop :=
  ∃ i : Fin n, i.val = 0 ∧ w i = d

/-- `d:prefix-bound`: true surviving prefixes avoid both the centre and the target. -/
def SurvivingPrefix {n : ℕ} (X : PairType) (d₀ : Compass) (w : DirectionWord n) : Prop :=
  IsTrail kernelStart kernelIncoming w ∧ FirstDirection w d₀ ∧
  ∀ j ≤ n, wordVertex kernelStart w j ≠ kernelCentre ∧ wordVertex kernelStart w j ≠ kernelTarget X

/-- Finite first-direction h-weighted closed-trail sum. -/
def firstDirectionPartialRow (X : PairType) (d₀ : Compass) (R : ℕ) : ℚ := by
  classical
  exact ∑ n ∈ Finset.Icc 1 R, ∑ w : DirectionWord n,
    if ClosedTrail X w ∧ FirstDirection w d₀ then closedContribution w else 0

/-- `d:prefix-bound`: exact short-order sum plus all surviving length-twelve phase prefixes.
A hit at time twelve belongs only to the short sum. -/
def stationaryPrefixBound (Q : MemoryQuotient 10 3741) (X : PairType) (d₀ : Compass)
    (C : StationaryData 3741) : ℚ := by
  classical
  exact firstDirectionPartialRow X d₀ 12 +
    ∑ w : DirectionWord 12, if SurvivingPrefix X d₀ w then
      ∑ φ : Phase, prefixPhases w φ * C.potential φ (Q.project (lastWindowWord 10 w))
        (wordVertex kernelStart w 12) else 0

/-- `p:stationary-check`: the five cases, with no symmetry reduction for row C. -/
def stationaryCases : Finset (PairType × Compass) :=
  {(.B, .north), (.B, .west), (.C, .north), (.C, .west), (.C, .south)}

/-- `p:stationary-check`: exact nine-decimal ceilings, after clearing denominators. -/
def stationaryPrefixCeiling (X : PairType) (d : Compass) : ℕ :=
  match X, d with
  | .B, .north => 351207554
  | .B, .west => 290599163
  | .C, .north => 527872005
  | .C, .west => 380754375
  | .C, .south => 273048088
  | _, _ => 0

/-- Corrected `d:stationary-walk` / `d:stationary-certificate`: every edge
into the centre is zero, including known-site rows. Legacy definitions are
retained for existing H3 row/refinement proofs. -/
def stationaryCoefficientV2 {m q : ℕ} (Q : MemoryQuotient m q) (X : PairType) (d₀ : Compass)
    (φ : Phase) (a : Fin q) (x : Plane) (d : Compass) (ψ : Phase) : ℚ :=
  if x = kernelCentre ∨ x = kernelTarget X ∨ Q.allowed a d = false ∨ x + d.step = kernelCentre then 0 else
    if x = kernelStart ∨ x = kernelStart + d₀.step then
      if ({x, x + d.step} : Finset Plane) = {kernelStart, kernelStart + d₀.step} ∨
        Q.kind a d = .revisit then 0 else if φ = ψ then 1 / 5 else 0
    else phaseTransition (Q.kind a d)
        (relaxedReward x (Q.arrival a) d {kernelCentre}) φ ψ

/-- Corrected `d:stationary-walk` / `d:stationary-certificate`: every edge
into the centre is zero, including known-site rows. Legacy definitions are
retained for existing H3 row/refinement proofs. -/
def stationaryApplyV2 {m q : ℕ} (Q : MemoryQuotient m q) (X : PairType) (d₀ : Compass)
    (F : Phase → Fin q → Plane → ℚ) (φ : Phase) (a : Fin q) (x : Plane) : ℚ :=
  ∑ d : Compass, ∑ ψ : Phase,
    stationaryCoefficientV2 Q X d₀ φ a x d ψ * F ψ (Q.successor a d) (x + d.step)

/-- Corrected `d:stationary-walk` / `d:stationary-certificate`: every edge
into the centre is zero, including known-site rows. Legacy definitions are
retained for existing H3 row/refinement proofs. -/
def StationaryData.PassesV2 {m q : ℕ} (C : StationaryData q) (Q : MemoryQuotient m q)
    (X : PairType) (d₀ : Compass) : Prop :=
  (∀ φ a, 0 < C.cap φ a) ∧
  (∀ a, certificateValueScale ≤ C.cap .C a ∧ certificateValueScale ≤ C.cap .D a) ∧
  (∀ φ a, (∑ d : Compass, ∑ ψ : Phase,
    coefficientCeiling (freeCoefficient Q φ a d ψ) * C.cap ψ (Q.successor a d)) ≤
      certificateCoefficientScale * C.cap φ a) ∧
  (∀ φ a x, C.value φ a x ≤ C.cap φ a) ∧
  (∀ φ a, C.extended φ a kernelCentre = 0 ∧
    (C.extended φ a (kernelTarget X) : ℚ) = certificateValueScale * phaseTerminal φ) ∧
  ∀ φ a (x : square (0, 0) certificateRadius),
    x.val ≠ kernelCentre → x.val ≠ kernelTarget X →
    (∑ d : Compass, ∑ ψ : Phase,
      coefficientCeiling (stationaryCoefficientV2 Q X d₀ φ a x.val d ψ) *
        C.extended ψ (Q.successor a d) (x.val + d.step)) ≤
      certificateCoefficientScale * C.value φ a x

end AKLT.Defs
