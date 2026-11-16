import CertData.H3.Bridge.Production

namespace AKLT.W.H3C052

open AKLT.Cert.H3.Production

/-- Join the 59 checked field batches to cover all 3741 states. -/
theorem main : CertData.H3.Bridge.FieldJoinLeaf := by
  intro G hReceipt
  have hpoint : ∀ a < 3741, fieldCheck G a = true := by
    intro a ha
    have hq : a / 64 < 59 := by omega
    have hrem : a % 64 < 64 := Nat.mod_lt _ (by decide)
    have hsplit : (a / 64) * 64 + a % 64 = a := by
      calc
        (a / 64) * 64 + a % 64 = a % 64 + 64 * (a / 64) := by omega
        _ = a := Nat.mod_add_div a 64
    have hroom : a % 64 < 3741 - (a / 64) * 64 := by omega
    have hidx : a % 64 < min 64 (3741 - (a / 64) * 64) :=
      Nat.lt_min.mpr ⟨hrem, hroom⟩
    have hb := hReceipt (⟨a / 64, hq⟩ : Fin 59)
    have hall : fieldBatch G ((a / 64) * 64)
        (min 64 (3741 - (a / 64) * 64)) = true := hb
    unfold fieldBatch at hall
    have hcheck := (List.all_eq_true.mp hall) (a % 64) (List.mem_range.mpr hidx)
    simpa [hsplit] using hcheck
  unfold fieldBatch
  apply List.all_eq_true.mpr
  intro a ha
  simpa using hpoint a (List.mem_range.mp ha)

#print axioms main

end AKLT.W.H3C052
