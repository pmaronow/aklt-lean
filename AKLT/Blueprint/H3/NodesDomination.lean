module
public import AKLT.Blueprint.H3.Basic

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.Blueprint.H3

/-- `l:stationary-domination`, lines 574–582: every remembered suffix is raw and
its next true edge is admitted. Restrict distinct bonds and translate the window origin. -/
def SuffixWindowValidityStatement : Prop :=
  ∀ n : ℕ, ∀ w : DirectionWord n, IsTrail kernelStart kernelIncoming w →
    ∀ i : Fin n, 10 ≤ i.val → RawWindow (suffixWindow w i.val) ∧
      WindowAdmissible (suffixWindow w i.val) (w i)

/-- `l:stationary-domination`, lines 574–582 and 612–619: update/arrival and kind labels.
Natural subtraction is used only after 10≤i; translate old departure vertices to compare revisits. -/
def SuffixWindowLabelsStatement : Prop :=
  ∀ n : ℕ, ∀ w : DirectionWord n, IsTrail kernelStart kernelIncoming w →
    ∀ i : Fin n, 10 ≤ i.val →
      windowSuccessor (suffixWindow w i.val) (w i) = suffixWindow w (i.val + 1) ∧
      windowArrival (suffixWindow w i.val) = wordIncoming kernelIncoming w i ∧
      (windowKind (suffixWindow w i.val) (w i) = .revisit → wordRevisit kernelStart w i = true) ∧
      (wordRevisit kernelStart w i = false → windowKind (suffixWindow w i.val) (w i) = trueKind w i)

/-- `l:stationary-domination`, lines 596–608: at most four used incident bonds.
Map each arrival and departure to its distinct unoriented bond incident at z; Compass gives four
neighbors. Consecutive arrivals/departures use distinct bonds because the whole word is a trail. -/
def IncidentBondBudgetStatement : Prop :=
  ∀ n : ℕ, ∀ w : DirectionWord n, IsTrail kernelStart kernelIncoming w → ∀ z : Plane,
    departureCount kernelStart w n z + arrivalCount w z ≤ 4

/-- `l:stationary-domination`, lines 596–608: finite path flow balance.
Match every departure except the possible initial one to its preceding arrival. This is a
counting inequality and includes the empty path and its terminal vertex. -/
def DepartureBalanceStatement : Prop :=
  ∀ n : ℕ, ∀ w : DirectionWord n, ∀ z : Plane,
    departureCount kernelStart w n z ≤ arrivalCount w z + 1

/-- `l:stationary-domination`, lines 584–610: permanent initial-site safety.
With at most two departures at each site, a suffix-time remembered revisit at either known
site would be a third departure: indices 0 and 1 are outside memory because L≥12.
The budget premise is a per-word counting fact, not another blueprint statement. -/
def KnownSiteMemoryStatement : Prop :=
  ∀ X : PairType, ∀ d₀ : Compass, d₀ ≠ .east → ∀ n L : ℕ, 12 ≤ L → L ≤ n →
    ∀ w : DirectionWord n, ClosedTrail X w → SurvivingPrefix X d₀ (takeWord w L) →
    (∀ z, departureCount kernelStart w n z ≤ 2) →
    ∀ i : Fin n, L ≤ i.val →
      (wordVertex kernelStart w i.val = kernelStart ∨
        wordVertex kernelStart w i.val = kernelStart + d₀.step) →
      wordRevisit kernelStart w i = true ∧ windowKind (suffixWindow w i.val) (w i) ≠ .revisit ∧
      ({wordVertex kernelStart w i.val, wordVertex kernelStart w i.val + (w i).step} : Finset Plane) ≠
        {kernelStart, kernelStart + d₀.step}

/-- `l:stationary-domination`, lines 621–639: the exact true reward is the finite
local rule with all truly dead neighbors removed; trail edges cannot immediately reverse.
Only the successor-vertex identity and definitions of the live sets are needed for the equality. -/
def TrueRewardIdentityStatement : Prop :=
  ∀ n : ℕ, ∀ w : DirectionWord n, IsTrail kernelStart kernelIncoming w → ∀ i : Fin n,
    w i ≠ (wordIncoming kernelIncoming w i).reverse ∧
    witnessKappa w i = relaxedReward (wordVertex kernelStart w i.val)
      (wordIncoming kernelIncoming w i) (w i) (trueDeadSet w i)

/-- `l:stationary-domination`, lines 621–639: forgetting dead neighbors increases reward.
Compare surviving two-element sets. Retained outgoing pairs increase from beta-prime to beta
when a second live neighbor is added; all added coefficients and both witness entries are positive. -/
def RewardForgettingStatement : Prop :=
  ∀ x : Plane, ∀ incoming outgoing : Compass, outgoing ≠ incoming.reverse →
    ∀ dead₁ dead₂ : Finset Plane, dead₁ ⊆ dead₂ →
      relaxedReward x incoming outgoing dead₂ ≤ relaxedReward x incoming outgoing dead₁

/-- Local facts sufficient for the scalar coefficient comparison, collected without any
blueprint-node hypotheses. Terminal avoidance includes the next vertex. -/
def TrueStepFacts {n : ℕ} (X : PairType) (d₀ : Compass) (w : DirectionWord n) (i : Fin n) : Prop :=
  RawWindow (suffixWindow w i.val) ∧ WindowAdmissible (suffixWindow w i.val) (w i) ∧
  windowArrival (suffixWindow w i.val) = wordIncoming kernelIncoming w i ∧
  (windowKind (suffixWindow w i.val) (w i) = .revisit → wordRevisit kernelStart w i = true) ∧
  (wordRevisit kernelStart w i = false → windowKind (suffixWindow w i.val) (w i) = trueKind w i) ∧
  witnessKappa w i ≤ relaxedReward (wordVertex kernelStart w i.val)
    (wordIncoming kernelIncoming w i) (w i) {kernelCentre} ∧
  wordVertex kernelStart w i.val ≠ kernelCentre ∧
  wordVertex kernelStart w i.val ≠ kernelTarget X ∧
  wordVertex kernelStart w i.val + (w i).step ≠ kernelCentre ∧
  ((wordVertex kernelStart w i.val = kernelStart ∨
      wordVertex kernelStart w i.val = kernelStart + d₀.step) →
    wordRevisit kernelStart w i = true ∧ windowKind (suffixWindow w i.val) (w i) ≠ .revisit ∧
    ({wordVertex kernelStart w i.val, wordVertex kernelStart w i.val + (w i).step} : Finset Plane) ≠
      {kernelStart, kernelStart + d₀.step})

/-- `l:stationary-domination`, lines 612–639: scalar phase-row comparison.
Use Correct to replace the raw labels. Split the stationary special-site condition, then
true/window revisit status. Forgotten revisits use 1/5≤1/3; first-visit phase changes use
reward monotonicity. The hypotheses are exactly the pointwise mathematical facts used. -/
def LocalCoefficientComparisonStatement : Prop :=
  ∀ Q : MemoryQuotient 10 3741, Q.Correct → ∀ X : PairType, ∀ d₀ : Compass,
    ∀ n : ℕ, ∀ w : DirectionWord n, ∀ i : Fin n, TrueStepFacts X d₀ w i →
      ∀ φ ψ : Phase, truePhaseCoefficient w i φ ψ ≤
        stationaryCoefficient Q X d₀ φ (Q.project (suffixWindow w i.val))
          (wordVertex kernelStart w i.val) (w i) ψ

/-- `l:stationary-domination`, lines 578–582: full true geometry used by the stopped
comparison. Center/target avoidance supplies all terminal exclusions; the next-vertex equality
is valid even on the last departure. This intentionally has no quotient premise. -/
def ClosedTrailStepGeometryStatement : Prop :=
  ∀ X : PairType, ∀ n : ℕ, ∀ w : DirectionWord n, ClosedTrail X w → ∀ i : Fin n,
    wordVertex kernelStart w (i.val + 1) = wordVertex kernelStart w i.val + (w i).step ∧
    wordVertex kernelStart w i.val ≠ kernelCentre ∧
    wordVertex kernelStart w i.val ≠ kernelTarget X ∧
    wordVertex kernelStart w (i.val + 1) ≠ kernelCentre

/-- `l:stationary-domination`, lines 641–647: a fixed true suffix is bounded by its
relaxed direction word. Induct along the suffix, using the two explicit pointwise premises
for weights and successor classes; append/take identities identify the initial state.
This is a matrix-product comparison, before any sum over words or lengths. -/
def SuffixWordComparisonStatement : Prop :=
  ∀ Q : MemoryQuotient 10 3741, Q.Correct → ∀ X : PairType, ∀ d₀ : Compass,
    ∀ L : ℕ, 12 ≤ L → ∀ P : DirectionWord L, ∀ r : ℕ, ∀ v : DirectionWord r,
      ClosedTrail X (appendWords P v) →
      (∀ i : Fin (L + r), L ≤ i.val → ∀ φ ψ : Phase,
        truePhaseCoefficient (appendWords P v) i φ ψ ≤
          stationaryCoefficient Q X d₀ φ (Q.project (suffixWindow (appendWords P v) i.val))
            (wordVertex kernelStart (appendWords P v) i.val) ((appendWords P v) i) ψ) →
      (∀ i : Fin (L + r), L ≤ i.val →
        Q.successor (Q.project (suffixWindow (appendWords P v) i.val)) ((appendWords P v) i) =
          Q.project (suffixWindow (appendWords P v) (i.val + 1))) →
      ∀ φ : Phase, truePhaseSuffix (appendWords P v) L φ ≤
        stationaryWordValue Q X d₀ (List.ofFn v) φ (Q.project (lastWindowWord 10 P))
          (wordVertex kernelStart P L)

/-- `l:stationary-domination`, lines 641–647, and `l:Bellman-soundness`, lines 677–684.
Expand one stationary iterate as the finite sum over absolute direction words; induction
on length retains every direction and next phase, including parallel quotient edges. -/
def StationaryWordExpansionStatement : Prop :=
  ∀ Q : MemoryQuotient 10 3741, ∀ X : PairType, ∀ d₀ : Compass, ∀ r : ℕ,
    ∀ φ : Phase, ∀ a : Fin 3741, ∀ x : Plane,
      ((stationaryApply Q X d₀)^[r]) (stationaryReward X) φ a x =
        ∑ v : DirectionWord r, stationaryWordValue Q X d₀ (List.ofFn v) φ a x

end AKLT.Blueprint.H3
