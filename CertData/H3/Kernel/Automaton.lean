import CertData.H3.Kernel.Common

namespace AKLT.Cert.H3
open AKLT.Defs

instance rawWindowDecidable {m : Nat} (w : DirectionWord m) : Decidable (RawWindow w) := by
  unfold RawWindow Function.Injective
  infer_instance
instance admissibleDecidable {m : Nat} (w : DirectionWord m) (d : Compass) :
    Decidable (WindowAdmissible w d) := by
  unfold WindowAdmissible
  infer_instance

/-- Exactly the per-raw-word conjunct of `MemoryQuotient.Correct`, including arrival. -/
def CorrectAt {m q : Nat} (Q : MemoryQuotient m q) (w : DirectionWord m) : Prop :=
  RawWindow w ∧ ∀ d : Compass,
    (Q.allowed (Q.project w) d = true ↔ WindowAdmissible w d) ∧
    (WindowAdmissible w d → Q.kind (Q.project w) d = windowKind w d ∧
      Q.successor (Q.project w) d = Q.project (windowSuccessor w d) ∧
      (windowKind w d ≠ .revisit → Q.arrival (Q.project w) = windowArrival w))

instance correctAtDecidable {m q : Nat} (Q : MemoryQuotient m q) (w : DirectionWord m) :
    Decidable (CorrectAt Q w) := by unfold CorrectAt; infer_instance

def rawRowCheck {m q : Nat} (Q : MemoryQuotient m q) (code : Nat) : Bool :=
  decide (CorrectAt Q (decodeWord m code))

theorem rawRowCheck_sound {m q code : Nat} {Q : MemoryQuotient m q}
    (h : rawRowCheck Q code = true) : CorrectAt Q (decodeWord m code) := of_decide_eq_true h

#print axioms rawRowCheck_sound
end AKLT.Cert.H3
