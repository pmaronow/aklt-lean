module
public import AKLT.Defs.Trails

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators ENNReal

namespace AKLT.Defs

/-- `d:kernel`: the fixed start, centre, target and incoming direction of each row. -/
def kernelStart : Plane := (-1, 0)
def kernelCentre : Plane := (0, 0)
def kernelTarget : PairType → Plane | .B => (1, 0) | .C => (0, 1)
def kernelIncoming : Compass := .west

/-- `d:kernel`: first hit of v, avoiding c, with no used unoriented bond repeated. -/
def ClosedTrail {n : ℕ} (X : PairType) (w : DirectionWord n) : Prop :=
  IsTrail kernelStart kernelIncoming w ∧ wordVertex kernelStart w n = kernelTarget X ∧
  (∀ j ≤ n, wordVertex kernelStart w j ≠ kernelCentre) ∧
  ∀ j < n, wordVertex kernelStart w j ≠ kernelTarget X

/-- `d:kernel`: dead sites are the centre and sites with two previous departures. -/
def deadAt {n : ℕ} (w : DirectionWord n) (i : Fin n) (z : Plane) : Prop :=
  z = kernelCentre ∨ 2 ≤ departureCount kernelStart w i.val z

/-- `d:kernel`: the three nonarrival neighbours, with the actual outgoing neighbour distinguished. -/
def responseNeighbours {n : ℕ} (w : DirectionWord n) (i : Fin n) : Finset Plane :=
  (neighbours (wordVertex kernelStart w i.val)).erase
    (wordVertex kernelStart w i.val - (wordIncoming kernelIncoming w i).step)

/-- Live non-outgoing neighbours; this is where the beta-prime case is decided. -/
def liveOtherNeighbours {n : ℕ} (w : DirectionWord n) (i : Fin n) : Finset Plane := by
  classical
  exact ((responseNeighbours w i).erase (wordVertex kernelStart w (i.val + 1))).filter
    fun z => ¬ deadAt w i z

/-- `d:kernel`: live response pairs, represented as two-element finite sets. -/
def responsePairs {n : ℕ} (w : DirectionWord n) (i : Fin n) : Finset (Finset Plane) :=
  (insert (wordVertex kernelStart w (i.val + 1)) (liveOtherNeighbours w i)).powersetCard 2

/-- `d:kernel`: exact type-dependent coefficient, including one-live-neighbour beta-prime. -/
def pairCoefficient {n : ℕ} (w : DirectionWord n) (i : Fin n) (p : Finset Plane) : ℚ :=
  let straight := wordStraight kernelIncoming w i
  if wordVertex kernelStart w (i.val + 1) ∈ p then
    if (liveOtherNeighbours w i).card = 1 then betaPrimeBound straight else betaBound straight
  else alphaBound straight

/-- Pair type is collinear exactly when both sites share a coordinate. -/
def responsePairType (p : Finset Plane) : PairType := by
  classical
  exact if ∀ x ∈ p, ∀ y ∈ p, x.1 = y.1 ∨ x.2 = y.2 then .B else .C

/-- `d:kernel`: the actual ambient shift, with maximum over the live pair. -/
def pairShift (X : PairType) (p : Finset Plane) : ℕ :=
  p.sup fun z => min (latticeDist z kernelStart) (latticeDist z (kernelTarget X))

/-- `d:kernel`: coefficients aggregated by pair type and exact shift. -/
def responseKappa {n : ℕ} (X Y : PairType) (s : ℕ) (w : DirectionWord n) (i : Fin n) : ℚ :=
  ∑ p ∈ responsePairs w i,
    if responsePairType p = Y ∧ pairShift X p = s then pairCoefficient w i p else 0

/-- `d:kernel-order`: the exact dyadic witness (not the rational 6/5). -/
def kernelWitness : PairType → ℚ
  | .B => 1
  | .C => 5404319552844595 / 4503599627370496

/-- `d:kernel-order`: the exact adopted contraction ceiling. -/
def kernelRho : ℚ := 993015 / 10^6

/-- `d:kernel-order`: the finite h-weighted reward at a departure. -/
def witnessKappa {n : ℕ} (w : DirectionWord n) (i : Fin n) : ℚ :=
  ∑ p ∈ responsePairs w i, pairCoefficient w i p * kernelWitness (responsePairType p)

/-- List of lattice first visits in path order. -/
def firstVisitList {n : ℕ} (w : DirectionWord n) : List (Fin n) :=
  (List.finRange n).filter fun i => !wordRevisit kernelStart w i

/-- `d:kernel-order`: comparison of short-order scores, with infinity for zero reward
and path-index tie breaking. -/
def shortOrderLE {n : ℕ} (w : DirectionWord n) (i j : Fin n) : Bool :=
  let ki := witnessKappa w i
  let kj := witnessKappa w j
  let xi := passageFactor (wordStraight kernelIncoming w i)
  let xj := passageFactor (wordStraight kernelIncoming w j)
  if ki = 0 then decide (kj = 0 ∧ i.val ≤ j.val)
  else if kj = 0 then true else
    let si := (xi - 1) / (xi * ki)
    let sj := (xj - 1) / (xj * kj)
    decide (si < sj ∨ (si = sj ∧ i.val ≤ j.val))

/-- `d:kernel-order`: the fixed cutoff-twelve ordering, independent of theta. -/
def kernelOrdering {n : ℕ} (w : DirectionWord n) : List (Fin n) :=
  let first := firstVisitList w
  if n ≤ 12 then first.mergeSort (shortOrderLE w) else
    first.filter (wordStraight kernelIncoming w) ++ first.filter (fun i => !wordStraight kernelIncoming w i)

/-- Exposure sum in a specified order: each reward gets every x up to and including its place. -/
def exposureSum {n : ℕ} (w : DirectionWord n) (reward : Fin n → ℚ) : List (Fin n) → ℚ
  | [] => 0
  | i :: rest => passageFactor (wordStraight kernelIncoming w i) * (reward i + exposureSum w reward rest)

/-- Exact finite h-weighted contribution of one closed trail. -/
def closedContribution {n : ℕ} (w : DirectionWord n) : ℚ :=
  trailBaseWeight kernelStart w * exposureSum w (witnessKappa w) (kernelOrdering w)

/-- `d:kernel`: one length's coefficient at a specified type and shift. -/
def kernelLengthCoefficient (X Y : PairType) (s n : ℕ) : ℚ := by
  classical
  exact ∑ w : DirectionWord n, if ClosedTrail X w then
    trailBaseWeight kernelStart w * exposureSum w (responseKappa X Y s w) (kernelOrdering w) else 0

/-- `d:kernel`: the nonnegative series M_XY,s. ENNReal prevents divergent tsum from becoming zero. -/
def shiftKernel (X Y : PairType) (s : ℕ) : ℝ≥0∞ :=
  ∑' n : ℕ, ENNReal.ofReal (kernelLengthCoefficient X Y s n : ℝ)

/-- `d:kernel`: the shifted kernel; finiteness is an explicit conclusion of l:Mtheta. -/
def shiftedKernel (θ : ℝ) (X Y : PairType) : ℝ≥0∞ :=
  ∑' s : ℕ, shiftKernel X Y s * ENNReal.ofReal (θ ^ (-(s : ℤ)))

/-- `h:H3`: a finite-cutoff row sum, with the exact fixed short/long orderings. -/
def kernelPartialRow (X : PairType) (R : ℕ) : ℚ := by
  classical
  exact ∑ n ∈ Finset.Icc 1 R, ∑ w : DirectionWord n,
    if ClosedTrail X w then closedContribution w else 0

/-- `h:H3`: every finite true-trail cutoff, rather than a finite numerical prefix. -/
def PositiveVectorBound : Prop :=
  ∀ X : PairType, ∀ R : ℕ, kernelPartialRow X R ≤ kernelRho * kernelWitness X

end AKLT.Defs
