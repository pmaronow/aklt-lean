import AKLT.Blueprint.Rec.NodesV2Closure
import AKLT.Blueprint.Top.ComputationV2

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.Blueprint.Rec

/-- `d:kernel-order`, §7 lines 579–585; REF2_5 finding 2. The domain
is the u-to-v first-hit kernel trail class ClosedTrail X, not graph cycles.
For n<=12 use the exact rational key, infinity for zero reward and path-index
tie breaking encoded by shortOrderLE. Sorting does not use the phase order. -/
def ShortKernelOrderingStatementV2 : Prop :=
  ∀ n : ℕ, ∀ X : PairType, ∀ w : DirectionWord n, ClosedTrail X w → n ≤ 12 →
    kernelOrdering w = (firstVisitList w).mergeSort (shortOrderLE w) ∧
      (kernelOrdering w).Pairwise (fun i j => shortOrderLE w i j = true)

/-- `d:kernel-order`, §7 lines 579–585; REF2_5 finding 2 and REF2_6
finding 2. Only n>12 uses straight-first, with increasing PATH index within
each type. This is exactly longOrdering, which the phase identity computes. -/
def LongKernelOrderingStatementV2 : Prop :=
  ∀ n : ℕ, ∀ X : PairType, ∀ w : DirectionWord n, ClosedTrail X w → 12 < n →
    kernelOrdering w = longOrdering w ∧
      ((firstVisitList w).filter (wordStraight kernelIncoming w)).Pairwise
        (fun i j => i.val < j.val) ∧
      ((firstVisitList w).filter (fun i => !wordStraight kernelIncoming w i)).Pairwise
        (fun i j => i.val < j.val)

end AKLT.Blueprint.Rec
