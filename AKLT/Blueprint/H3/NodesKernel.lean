module
public import AKLT.Blueprint.H3.Positivity

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators ENNReal
open AKLT.Defs

namespace AKLT.Blueprint.H3

/-- `l:stationary-assembly`, lines 1188–1196: disjoint first-direction partition.
At positive length the first index exists; east enters the center and is excluded. Empty
cutoff sums vanish. No symmetry is used for C. -/
def FirstDirectionPartitionStatement : Prop :=
  ∀ X : PairType, ∀ R : ℕ,
    kernelPartialRow X R = firstDirectionPartialRow X .north R +
      firstDirectionPartialRow X .west R + firstDirectionPartialRow X .south R

/-- `h:H3`, PLAN.md:2146–2164, nonnegative-series equivalence.
All pair shifts at fixed length belong to the explicit finite set lengthShifts. Prove
zero for every responseKappa outside that set and propagate zero through exposureSum. -/
def LengthShiftSupportStatement : Prop :=
  ∀ X Y : PairType, ∀ n s : ℕ, s ∉ lengthShifts X n → kernelLengthCoefficient X Y s n = 0

/-- `h:H3`, PLAN.md:2146–2164, and `d:kernel`.
Regroup each finite live-pair sum by its actual type and exact shift, then use linearity
of exposureSum in its reward. Commute the finite word, type, and shift sums. No analytic
convergence statement is needed at one fixed length. -/
def LengthRewardPartitionStatement : Prop :=
  ∀ X : PairType, ∀ n : ℕ,
    kernelLengthRow X n = ∑ Y : PairType, ∑ s ∈ lengthShifts X n,
      kernelLengthCoefficient X Y s n * kernelWitness Y

/-- `h:H3`: the zero-length row vanishes, because u differs from both possible targets. -/
theorem kernelLengthRow_zero (X : PairType) : kernelLengthRow X 0 = 0 := by
  classical
  have hn : ∀ w : DirectionWord 0, ¬ ClosedTrail X w := by
    intro w h
    have he := h.2.1
    cases X <;> norm_num [wordVertex, kernelStart, kernelTarget] at he
  simp [kernelLengthRow, hn]

/-- `h:H3`: the finite-cutoff row is exactly the positive-length partial sum. -/
theorem kernelPartialRow_eq_sum (X : PairType) (R : ℕ) :
    kernelPartialRow X R = ∑ n ∈ Finset.Icc 1 R, kernelLengthRow X n := rfl

end AKLT.Blueprint.H3

namespace AKLT.Blueprint.H3

/-- `h:H3`, PLAN.md:2146–2164: exchange nonnegative sums and remove the finite shift
support restriction at each length. Apply ENNReal tsum commutation, ofReal of nonnegative
finite sums, and theta=1. No summability hypothesis is appropriate for ENNReal. -/
def KernelSeriesRegroupingStatement : Prop :=
  ∀ X : PairType,
    (∀ Y : PairType, ∀ n s : ℕ, s ∉ lengthShifts X n → kernelLengthCoefficient X Y s n = 0) →
    (∀ n : ℕ, kernelLengthRow X n = ∑ Y : PairType, ∑ s ∈ lengthShifts X n,
      kernelLengthCoefficient X Y s n * kernelWitness Y) →
    (∑ Y : PairType, shiftedKernel 1 X Y * ENNReal.ofReal (kernelWitness Y : ℝ)) =
      ∑' n : ℕ, ENNReal.ofReal (kernelLengthRow X n : ℝ)

/-- `h:H3`, PLAN.md:2146–2164: finite cutoffs control the full nonnegative series.
Use tsum_eq_iSup_nat. The f(0)=0 premise accounts for Icc 1 R instead of range R;
nonnegativity permits enlarging the last endpoint. Cutoff zero forces B≥0. -/
def CutoffSeriesLiftStatement : Prop :=
  ∀ f : ℕ → ℚ, (∀ n, 0 ≤ f n) → f 0 = 0 → ∀ B : ℚ,
    (∀ R : ℕ, (∑ n ∈ Finset.Icc 1 R, f n) ≤ B) →
      (∑' n : ℕ, ENNReal.ofReal (f n : ℝ)) ≤ ENNReal.ofReal (B : ℝ)

end AKLT.Blueprint.H3
