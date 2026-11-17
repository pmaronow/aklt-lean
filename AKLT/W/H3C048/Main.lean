module
public import CertData.H3.Bridge.Production

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

namespace AKLT.W.H3C048

open AKLT.Gen.Packed
open CertData.H3.Bridge

private theorem lane_chunk (P i j : Nat) (hj : j < 4096) :
    lane (lane P 49152 i) 12 j = lane P 12 (i * 4096 + j) := by
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < 12
  · have hsmall : 12 * j + k < 49152 := by omega
    simp [AKLT.Gen.Packed.testBit_lane, hk, hsmall]
    congr 1
    ring
  · simp [AKLT.Gen.Packed.testBit_lane, hk]

theorem main : CertData.H3.Bridge.ClassDataLeaf := by
  intro P htrans hblocks c
  have hc : c.val < 1048576 := by
    have h := c.isLt
    norm_num [pow_succ] at h ⊢
    exact h
  have hi : c.val / 4096 < 256 := by omega
  have hj : c.val % 4096 < 4096 := Nat.mod_lt _ (by omega)
  have hcheck : (List.range 256).all
      (fun i => P.blocks.get i == lane P.denseClass 49152 i) = true := by
    simpa [PackedGraph.blockCheck] using hblocks
  have hblock := (List.all_eq_true.mp hcheck) (c.val / 4096)
    (List.mem_range.mpr hi)
  have hblock' : P.blocks.get (c.val / 4096) =
      lane P.denseClass 49152 (c.val / 4096) := by
    exact beq_iff_eq.mp hblock
  have hdense : P.denseClass = AKLT.Defs.Automaton10Data.rawClass := htrans.1
  have hchunk := lane_chunk AKLT.Defs.Automaton10Data.rawClass
      (c.val / 4096) (c.val % 4096) hj
  have hdiv : c.val / 4096 * 4096 + c.val % 4096 = c.val := by
    have := Nat.mod_add_div c.val 4096
    omega
  change P.classAt c.val = AKLT.Defs.Automaton10Data.rawClassAt c.val
  simp only [PackedGraph.classAt, if_pos hc]
  rw [hblock', hdense, hchunk, hdiv]
  rw [AKLT.Defs.Automaton10Data.rawClassAt]
  simp [AKLT.Defs.Automaton10Data.lane, AKLT.Gen.Packed.lane,
    Nat.shiftRight_eq_div_pow]

#print axioms main

end AKLT.W.H3C048
