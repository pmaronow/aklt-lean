module
public import CertData.H3.Bridge.Production

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

namespace AKLT.W.H3C054

open CertData.H3.Bridge
open AKLT.Cert.H3.Production

/-- The sixty-four-wide receipts cover the complete representative table. -/
theorem main : CertData.H3.Bridge.RepresentativeJoinLeaf := by
  intro G hReceipt
  unfold representativeBatch
  apply List.all_eq_true.mpr
  intro a ha
  have haBound : a < 3741 := List.mem_range.mp ha
  let batch : Nat := a / 64
  let offset : Nat := a % 64
  have hdecomp : batch * 64 + offset = a := by
    dsimp [batch, offset]
    omega
  have hoffset : offset < 64 := by
    dsimp [offset]
    exact Nat.mod_lt _ (by decide)
  have hbatchBound : batch < 59 := by
    dsimp [batch]
    omega
  let i : Fin 59 := ⟨batch, hbatchBound⟩
  have hremain : offset < 3741 - batch * 64 := by
    omega
  have hoffsetCount : offset < min 64 (3741 - batch * 64) :=
    Nat.lt_min.mpr ⟨hoffset, hremain⟩
  have hchunk := hReceipt i
  unfold representativeBatch at hchunk
  have hchunkAll := (List.all_eq_true.mp hchunk) offset
    (List.mem_range.mpr hoffsetCount)
  simpa [i, hdecomp] using hchunkAll

end AKLT.W.H3C054

#print axioms AKLT.W.H3C054.main
