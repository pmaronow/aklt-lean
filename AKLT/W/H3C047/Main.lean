module
public import CertData.H3.Bridge.Production

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

namespace AKLT.W.H3C047

open AKLT.Gen.Packed
open CertData.H3.Bridge

theorem main : CertData.H3.Bridge.SpanDataLeaf := by
  intro P
  intro start count hcount hblock htotal
  constructor
  · change P.classSpan start count < 2 ^ (12 * count)
    unfold PackedGraph.classSpan
    have hmask :
        Nat.land (P.blocks.get (start / 4096) >>> (12 * (start % 4096)))
          (2 ^ (12 * count) - 1) ≤ 2 ^ (12 * count) - 1 :=
      Nat.and_le_right
    have hlt : 2 ^ (12 * count) - 1 < 2 ^ (12 * count) := by
      exact Nat.sub_lt (by positivity) (by omega)
    exact lt_of_le_of_lt hmask hlt
  · intro i hi
    have hcode : start + i < 1048576 := by omega
    have hrem : start % 4096 + i < 4096 := by omega
    have hdiv : (start + i) / 4096 = start / 4096 := by
      have hs := Nat.mod_add_div start 4096
      omega
    have hmod : (start + i) % 4096 = start % 4096 + i := by
      have hs := Nat.mod_add_div start 4096
      omega
    change lane (P.classSpan start count) 12 i = P.classAt (start + i)
    change lane
      (Nat.land (P.blocks.get (start / 4096) >>> (12 * (start % 4096)))
        (2 ^ (12 * count) - 1)) 12 i = P.classAt (start + i)
    rw [AKLT.Gen.Packed.lane_truncate _ 12 count i (by omega)]
    rw [if_pos hi]
    rw [AKLT.Gen.Packed.lane_shiftRight]
    unfold PackedGraph.classAt
    rw [if_pos hcode, hdiv, hmod]
    simp [Nat.add_comm]

#print axioms main

end AKLT.W.H3C047
