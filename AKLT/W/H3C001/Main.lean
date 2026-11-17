module
public import CertData.H3.Bridge.Interface

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

namespace AKLT.W.H3C001

open AKLT.Cert.H3 AKLT.Defs

private theorem directionCode_direction_mod (x : Nat) :
    directionCode (direction (x % 4)) = x % 4 := by
  have hlt : x % 4 < 4 := Nat.mod_lt _ (by decide)
  have hcases : x % 4 = 0 ∨ x % 4 = 1 ∨ x % 4 = 2 ∨ x % 4 = 3 := by omega
  rcases hcases with h | h | h | h <;> simp [direction, directionCode, h]

private theorem directionCode_decodeWord (n c : Nat) (i : Fin n) :
    directionCode (decodeWord n c i) = (c / 4^(n-1-i.val)) % 4 := by
  exact directionCode_direction_mod _

private theorem encodeWord_succ {n : Nat} (w : DirectionWord (n+1)) :
    encodeWord w = directionCode (w 0) * 4^n +
      encodeWord (fun i : Fin n => w i.succ) := by
  simp only [encodeWord, List.finRange_succ, List.map_cons, List.sum_cons,
    List.map_map, Function.comp_def]
  have hzero : n + 1 - 1 - 0 = n := by omega
  have htail :
      List.map (fun x : Fin n => directionCode (w x.succ) * 4^(n+1-1-(x.succ).val))
          (List.finRange n) =
        List.map (fun i : Fin n => directionCode (w i.succ) * 4^(n-1-i.val))
          (List.finRange n) := by
    apply List.map_congr_left
    intro i hi
    have hbound := i.isLt
    have hidx : n + 1 - 1 - (i.val + 1) = n - 1 - i.val := by omega
    rw [Fin.val_succ, hidx]
  rw [Fin.val_zero, hzero, htail]

private theorem mod_div_base4 (c k : Nat) (hk : 0 < k) :
    (c / k % 4) * k + c % k = c % (4*k) := by
  let q := c / k
  let r := c % k
  have hc : r + k*q = c := by
    dsimp [q, r]
    exact Nat.mod_add_div c k
  have hq : q % 4 + 4*(q / 4) = q := Nat.mod_add_div q 4
  have hr : r < k := by
    dsimp [r]
    exact Nat.mod_lt _ hk
  have hqmod : q % 4 < 4 := Nat.mod_lt _ (by decide)
  have hsmall : q % 4 * k + r < 4*k := by
    have hq3 : q % 4 ≤ 3 := by omega
    have hm : q % 4 * k ≤ 3*k := Nat.mul_le_mul_right k hq3
    omega
  have hsplit : c = (q % 4 * k + r) + (4*k)*(q / 4) := by
    calc
      c = r + k*q := hc.symm
      _ = r + k*(q % 4 + 4*(q/4)) := congrArg (fun z => r + k*z) hq.symm
      _ = (q % 4 * k + r) + (4*k)*(q/4) := by ring
  symm
  calc
    c % (4*k) = ((q % 4 * k + r) + (4*k)*(q/4)) % (4*k) := by rw [hsplit]
    _ = (q % 4 * k + r) % (4*k) := Nat.add_mul_mod_self_left _ _ _
    _ = q % 4 * k + r := Nat.mod_eq_of_lt hsmall

private theorem encode_decode_mod (n c : Nat) :
    encodeWord (decodeWord n c) = c % 4^n := by
  induction n generalizing c with
  | zero =>
      change 0 = c % 1
      exact (Nat.mod_one c).symm
  | succ n ih =>
      rw [encodeWord_succ]
      have hhead : directionCode (decodeWord (n+1) c 0) = (c / 4^n) % 4 := by
        rw [directionCode_decodeWord]
        congr 2
      have htail : (fun i : Fin n => decodeWord (n+1) c i.succ) = decodeWord n c := by
        funext i
        simp only [decodeWord, Fin.val_succ]
        have hbound := i.isLt
        have hidx : n + 1 - 1 - (i.val + 1) = n - 1 - i.val := by omega
        rw [hidx]
      rw [hhead, htail, ih]
      have hk : 0 < 4^n := Nat.pow_pos (by decide)
      simpa [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
        (mod_div_base4 c (4^n) hk)

theorem main : CertData.H3.Bridge.CodeDecodeLeaf := by
  intro n c hc
  rw [encode_decode_mod]
  exact Nat.mod_eq_of_lt hc

#print axioms main

end AKLT.W.H3C001
