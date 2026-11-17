module
public import CertData.H3.Bridge.Interface

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

namespace AKLT.W.H3C002

open AKLT.Cert.H3 AKLT.Defs

private theorem directionCode_lt_four (d : Compass) : directionCode d < 4 := by
  cases d <;> decide

private theorem direction_directionCode (d : Compass) : direction (directionCode d) = d := by
  cases d <;> rfl

private theorem encodeWord_succ {n : Nat} (w : DirectionWord (n + 1)) :
    encodeWord w = directionCode (w 0) * 4^n + encodeWord (fun i => w i.succ) := by
  simp only [encodeWord, List.finRange_succ, List.map_cons, List.sum_cons,
    List.map_map]
  change directionCode (w 0) * 4^n +
    (List.map (fun i : Fin n => directionCode (w i.succ) * 4^(n - i.succ.val))
      (List.finRange n)).sum = _
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro i hi
  congr 2; simp [Fin.val_succ]; omega

private theorem encodeWord_lt_pow {n : Nat} (w : DirectionWord n) : encodeWord w < 4^n := by
  induction n with
  | zero => simp [encodeWord]
  | succ n ih =>
      rw [encodeWord_succ]
      have hd : directionCode (w 0) ≤ 3 := Nat.le_of_lt_succ (directionCode_lt_four _)
      have hmul : directionCode (w 0) * 4^n ≤ 3 * 4^n := Nat.mul_le_mul_right _ hd
      have htail : encodeWord (fun i => w i.succ) < 4^n := ih (fun i => w i.succ)
      have hsum : 3 * 4^n + encodeWord (fun i => w i.succ) < 4 * 4^n := by omega
      have hlt : directionCode (w 0) * 4^n + encodeWord (fun i => w i.succ) < 4 * 4^n := by omega
      simpa [pow_succ, Nat.mul_comm] using hlt

private theorem baseDigit_split (n k d t : Nat) (hk : k ≤ n) (ht : t < 4^n) :
    ((d * 4^n + t) / 4^k) % 4 =
      if k = n then d % 4 else (t / 4^k) % 4 := by
  have hpow : 4^n = 4^k * 4^(n-k) := by
    calc
      4^n = 4^(k + (n-k)) := congrArg (fun x : Nat => 4^x) (Nat.add_sub_of_le hk).symm
      _ = 4^k * 4^(n-k) := by rw [Nat.pow_add]
  have hdiv : (d * 4^n + t) / 4^k = d * 4^(n-k) + t / 4^k := by
    rw [show d * 4^n + t = 4^k * (d * 4^(n-k)) + t by rw [hpow]; ring]
    exact Nat.mul_add_div (by positivity) _ _
  by_cases hkn : k = n
  · subst k
    have htdiv : t / 4^n = 0 := Nat.div_eq_of_lt ht
    simp [hdiv, htdiv]
  · have hlt : k < n := by omega
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n-k ≠ 0)
    rw [hdiv, hj, pow_succ]
    simp [hkn, Nat.add_mod, Nat.mul_mod]

private theorem decode_encode_succ {n : Nat} (w : DirectionWord (n + 1))
    (htail : decodeWord n (encodeWord (fun i => w i.succ)) = (fun i => w i.succ)) :
    decodeWord (n + 1) (encodeWord w) = w := by
  rw [encodeWord_succ]
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · have he : n + 1 - 1 = n := by omega
    change direction (((directionCode (w 0) * 4^n + encodeWord (fun i => w i.succ)) / 4^(n+1-1)) % 4) = w 0
    rw [he, baseDigit_split n n (directionCode (w 0)) (encodeWord (fun i => w i.succ)) le_rfl
      (encodeWord_lt_pow (fun i => w i.succ))]
    simp [Nat.mod_eq_of_lt (directionCode_lt_four _), direction_directionCode]
  · have he : n + 1 - 1 - (j.val + 1) = n - 1 - j.val := by omega
    change direction (((directionCode (w 0) * 4^n + encodeWord (fun i => w i.succ)) /
      4^(n+1-1-(j.val+1))) % 4) = w j.succ
    rw [he, baseDigit_split n (n-1-j.val) (directionCode (w 0))
      (encodeWord (fun i => w i.succ)) (by omega)
      (encodeWord_lt_pow (fun i => w i.succ))]
    have hk : n - 1 - j.val ≠ n := by omega
    simp [hk]
    exact congrFun htail j

theorem main : CertData.H3.Bridge.CodeEncodeLeaf := by
  intro n
  induction n with
  | zero =>
      intro w
      constructor
      · simp [encodeWord]
      · funext i
        exact Fin.elim0 i
  | succ n ih =>
      intro w
      constructor
      · exact encodeWord_lt_pow w
      · exact decode_encode_succ w ((ih (fun i => w i.succ)).2)

#print axioms main

end AKLT.W.H3C002
