import CertData.H3.Bridge.Interface
import AKLT.Cert.H2.Words

namespace AKLT.W.H3C003

open AKLT.Defs AKLT.Cert.H3 AKLT.Cert.H2

theorem encode_drop_first {n : Nat} (w : DirectionWord (n + 1)) :
    encodeWord w = directionCode (w 0) * 4^n +
      encodeWord (fun i => w i.succ) := by
  simp only [encodeWord, List.finRange_succ, List.map_cons, List.sum_cons]
  congr 1
  simp only [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i hi
  simp only [Function.comp_apply, Fin.val_succ]
  change directionCode (w i.succ) * 4^(n - (i.val + 1)) =
    directionCode (w i.succ) * 4^(n - 1 - i.val)
  have hi' := i.isLt
  have he : n - (i.val + 1) = n - 1 - i.val := by omega
  rw [he]

theorem encode_snoc {n : Nat} (w : DirectionWord n) (d : Compass) :
    encodeWord (snoc w d) = 4 * encodeWord w + directionCode d := by
  induction n with
  | zero => simp [encodeWord, snoc, Fin.snoc]
  | succ n ih =>
      have h := encode_drop_first (snoc w d)
      have ht : (fun i : Fin (n + 1) => snoc w d i.succ) = snoc (fun i => w i.succ) d := by
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp [snoc, Fin.snoc]
        · have hidx : j.castSucc.succ = (Fin.succ j).castSucc := Fin.ext rfl
          simp only [snoc, Fin.snoc_castSucc, hidx]
      rw [h, ht]
      rw [ih]
      have hw := encode_drop_first w
      rw [hw]
      simp [snoc, Fin.snoc, Nat.pow_succ, mul_add, add_assoc]
      ring

theorem directionCode_lt_four (d : Compass) : directionCode d < 4 := by
  cases d <;> decide

theorem encodeWord_lt : ∀ n (w : DirectionWord n), encodeWord w < 4^n := by
  intro n
  induction n with
  | zero =>
      intro w
      simp [encodeWord]
  | succ n ih =>
      intro w
      rw [encode_drop_first w]
      have htail := ih (fun i => w i.succ)
      have hd := directionCode_lt_four (w 0)
      have hadd := Nat.add_lt_add_left htail (directionCode (w 0) * 4^n)
      have hdle : directionCode (w 0) ≤ 3 := by omega
      have hmul := Nat.mul_le_mul_right (4^n) (Nat.add_le_add_right hdle 1)
      calc
        directionCode (w 0) * 4^n + encodeWord (fun i => w i.succ)
            < directionCode (w 0) * 4^n + 4^n := hadd
        _ = (directionCode (w 0) + 1) * 4^n := by ring
        _ ≤ 4 * 4^n := hmul
        _ = 4^(n+1) := by rw [Nat.pow_succ]; ring

theorem encode_windowSuccessor_mod (v : DirectionWord 10) (d : Compass) :
    encodeWord (windowSuccessor v d) =
      (encodeWord v * 4 + directionCode d) % 4^10 := by
  let tail : DirectionWord 9 := fun i => v i.succ
  have hwindow : windowSuccessor v d = snoc tail d := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [windowSuccessor, snoc, Fin.snoc]
    · have hj : j.val + 1 < 10 := by omega
      simp only [windowSuccessor, Fin.val_castSucc, dite_eq_left (by simpa using hj),
        snoc, Fin.snoc_castSucc, tail]
      apply congrArg v
      apply Fin.ext
      rfl
  have hdrop := encode_drop_first v
  have hfull : encodeWord v * 4 + directionCode d =
      directionCode (v 0) * 4^10 + encodeWord (windowSuccessor v d) := by
    rw [hdrop, hwindow, encode_snoc]
    rw [Nat.pow_succ]
    ring
  have hlt := encodeWord_lt 10 (windowSuccessor v d)
  rw [hfull, Nat.add_comm (directionCode (v 0) * 4^10) (encodeWord (windowSuccessor v d)),
    Nat.mul_comm (directionCode (v 0)) (4^10), Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt hlt]

theorem mod_append_four (n d m : Nat) :
    (n % m * 4 + d) % m = (n * 4 + d) % m := by
  simp [Nat.add_mod, Nat.mul_mod]

theorem lastWindowCode_aux : ∀ n (w : DirectionWord (10 + n)),
    encodeWord (lastWindowWord 10 w) = encodeWord w % 4^10 := by
  intro n
  induction n with
  | zero =>
      intro w
      have hwindow : lastWindowWord 10 w = w := by
        funext i
        simp [lastWindowWord]
      rw [hwindow]
      exact (Nat.mod_eq_of_lt (encodeWord_lt 10 w)).symm
  | succ n ih =>
      intro w
      let pre : DirectionWord (10 + n) := fun i => w i.castSucc
      let d : Compass := w (Fin.last (10 + n))
      have hword : w = snoc pre d := by
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp [pre, d, snoc]
        · simp [pre, snoc]
      rw [hword, lastWindow_snoc (m := 10) pre d (by decide) (by omega)]
      rw [encode_windowSuccessor_mod, ih pre]
      rw [encode_snoc]
      simpa [Nat.mul_comm] using
        mod_append_four (encodeWord pre) (directionCode d) 1048576

theorem main : CertData.H3.Bridge.LastWindowCodeLeaf := by
  intro n hn w
  have hlen : ∃ k, n = 10 + k := by
    refine ⟨n - 10, ?_⟩
    omega
  rcases hlen with ⟨k, rfl⟩
  exact lastWindowCode_aux k w

#print axioms AKLT.W.H3C003.main

end AKLT.W.H3C003
