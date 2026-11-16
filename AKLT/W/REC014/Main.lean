import AKLT.W.REC014.Positive
import AKLT.W.REC014.Integral

noncomputable section
open AKLT.Defs

namespace AKLT.W.REC014

/-- With a single outgoing bond, summing the departure spin gives one before
and after tracing. The common partition is strictly positive. -/
theorem main : AKLT.Blueprint.Rec.OneStepTrivialStatement := by
  intro a hy hc
  have h (b : Bool) : stepRatio a.D a.τ b a.y a.o = 1 := by
    simp only [stepRatio, traceRatio, traceNetwork]
    rw [partition_collapse a hy hc b]
    exact div_self (ne_of_gt (partition_positive a.D a.τ b))
  exact ⟨h true, h false⟩

end AKLT.W.REC014

#print axioms AKLT.W.REC014.main
