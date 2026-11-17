module
public import CertData.H3.Bridge.Interface

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

namespace AKLT.W.H3C004

open AKLT.Cert.H3 AKLT.Defs CertData.H3.Bridge

private theorem directionCode_direction_mod (n : Nat) :
    directionCode (direction (n % 4)) = n % 4 := by
  have hn : n % 4 < 4 := Nat.mod_lt _ (by decide)
  interval_cases h : n % 4 <;> simp [direction, directionCode]

theorem main : CertData.H3.Bridge.SuccessorCodeLeaf := by
  intro c hc d
  fin_cases d
  all_goals
    simp [encodeWord, windowSuccessor, decodeWord, List.finRange]
    simp_rw [directionCode_direction_mod]
    simp [direction, directionCode]
    have h0 : c % 4 + 4 * (c / 4) = c := Nat.mod_add_div _ _
    have h1 : (c / 4) % 4 + 4 * (c / 16) = c / 4 := by
      simpa [Nat.div_div_eq_div_mul] using (Nat.mod_add_div (c / 4) 4)
    have h2 : (c / 16) % 4 + 4 * (c / 64) = c / 16 := by
      simpa [Nat.div_div_eq_div_mul] using (Nat.mod_add_div (c / 16) 4)
    have h3 : (c / 64) % 4 + 4 * (c / 256) = c / 64 := by
      simpa [Nat.div_div_eq_div_mul] using (Nat.mod_add_div (c / 64) 4)
    have h4 : (c / 256) % 4 + 4 * (c / 1024) = c / 256 := by
      simpa [Nat.div_div_eq_div_mul] using (Nat.mod_add_div (c / 256) 4)
    have h5 : (c / 1024) % 4 + 4 * (c / 4096) = c / 1024 := by
      simpa [Nat.div_div_eq_div_mul] using (Nat.mod_add_div (c / 1024) 4)
    have h6 : (c / 4096) % 4 + 4 * (c / 16384) = c / 4096 := by
      simpa [Nat.div_div_eq_div_mul] using (Nat.mod_add_div (c / 4096) 4)
    have h7 : (c / 16384) % 4 + 4 * (c / 65536) = c / 16384 := by
      simpa [Nat.div_div_eq_div_mul] using (Nat.mod_add_div (c / 16384) 4)
    have h8 : (c / 65536) % 4 + 4 * (c / 262144) = c / 65536 := by
      simpa [Nat.div_div_eq_div_mul] using (Nat.mod_add_div (c / 65536) 4)
    omega

end AKLT.W.H3C004

#print axioms AKLT.W.H3C004.main
