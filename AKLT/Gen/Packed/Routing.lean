import AKLT.Gen.Packed.Basic
namespace AKLT.Gen.Packed

theorem testBit_lane (P b s i : Nat) :
    (lane P b s).testBit i = (decide (i < b) && P.testBit (b*s+i)) := by
  simp [lane]

theorem lane_land (P Q b s : Nat) :
    lane (Nat.land P Q) b s = Nat.land (lane P b s) (lane Q b s) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [testBit_lane, Nat.land_eq, Nat.testBit_and]
  cases decide (i < b) <;> simp

/-- Right shift by whole lanes; no wrap. -/
theorem lane_shiftRight (P b k s : Nat) :
    lane (P >>> (b*k)) b s = lane P b (s+k) := by
  simp only [lane, ← Nat.shiftRight_add]
  congr 2
  ring

/-- Left shift by whole lanes inserts zero lanes. -/
theorem lane_shiftLeft (P b k s : Nat) (hb : 0 < b) :
    lane (P <<< (b*k)) b s = if k ≤ s then lane P b (s-k) else 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < b
  · by_cases hs : k ≤ s
    · have hle : b*k ≤ b*s+i := by nlinarith
      have hmul : b*k ≤ b*s := Nat.mul_le_mul_left b hs
      have he : b*s+i-b*k = b*(s-k)+i := by rw [Nat.mul_sub_left_distrib]; omega
      simp [testBit_lane, hi, hs, hle, he]
    · have hlt : b*s+i < b*k := by
        have hsk : s+1 ≤ k := by omega
        nlinarith
      simp [testBit_lane, hi, hs, Nat.not_le_of_gt hlt]
  · simp only [testBit_lane, hi, decide_false, Bool.false_and]
    split <;> simp [testBit_lane, hi]

/-- Select complete lanes using a Boolean predicate. -/
def laneMask (b n : Nat) (p : Nat → Bool) : Nat :=
  packFn b n (fun s => if p s then 2 ^ b - 1 else 0)

theorem lane_laneMask (b n : Nat) (p : Nat → Bool) (s : Nat) :
    lane (laneMask b n p) b s = if s < n ∧ p s = true then 2 ^ b - 1 else 0 := by
  rw [laneMask, lane_packFn]
  · split_ifs <;> simp_all
  · intro i hi
    have : 0 < 2 ^ b := by positivity
    split <;> omega

theorem lane_mask (P b n : Nat) (p : Nat → Bool) (s : Nat) :
    lane (Nat.land P (laneMask b n p)) b s =
      if s < n ∧ p s = true then lane P b s else 0 := by
  rw [lane_land, lane_laneMask]
  split_ifs
  · exact Nat.and_two_pow_sub_one_of_lt_two_pow (lane_lt P b s)
  · simp

/-- Row-major square indexing: `row * w + col`. -/
def gridIndex (w row col : Nat) : Nat := row*w+col

/-- Output mask for a rightward move: remove the leftmost column. -/
def rightMask (b w : Nat) : Nat := laneMask b (w*w) (fun s => decide (0 < s % w))
/-- Output mask for a leftward move: remove the rightmost column. -/
def leftMask (b w : Nat) : Nat := laneMask b (w*w) (fun s => decide (s % w + 1 < w))
/-- Output mask selecting exactly row `r`. -/
def rowMask (b w r : Nat) : Nat := laneMask b (w*w) (fun s => decide (s / w = r))
/-- Output mask selecting exactly column `c`. -/
def columnMask (b w c : Nat) : Nat := laneMask b (w*w) (fun s => decide (s % w = c))

def moveRight (P b w : Nat) : Nat := Nat.land (P <<< b) (rightMask b w)
def moveLeft (P b w : Nat) : Nat := Nat.land (P >>> b) (leftMask b w)
def moveDown (P b w : Nat) : Nat := Nat.land (P <<< (b*w)) (2 ^ (b*(w*w))-1)
def moveUp (P b w : Nat) : Nat := Nat.land (P >>> (b*w)) (2 ^ (b*(w*w))-1)

theorem lane_moveRight (P b w s : Nat) (hb : 0 < b) :
    lane (moveRight P b w) b s =
      if s < w*w ∧ 0 < s % w then lane P b (s-1) else 0 := by
  unfold moveRight rightMask
  rw [lane_mask]
  simp only [decide_eq_true_eq]
  split_ifs with h
  · have hs : 1 ≤ s := by have := Nat.mod_le s w; omega
    simpa [lane_shiftLeft P b 1 s hb, hs] using
      (lane_shiftLeft P b 1 s hb)
  · rfl

theorem lane_moveLeft (P b w s : Nat) :
    lane (moveLeft P b w) b s =
      if s < w*w ∧ s % w + 1 < w then lane P b (s+1) else 0 := by
  unfold moveLeft leftMask
  rw [lane_mask]
  simpa using congrArg (fun q => if s < w*w ∧ s%w+1<w then q else 0)
    (lane_shiftRight P b 1 s)

/-- A finite-width low mask truncates complete lanes. -/
theorem lane_truncate (P b n s : Nat) (hb : 0 < b) :
    lane (Nat.land P (2^(b*n)-1)) b s = if s < n then lane P b s else 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < b
  · by_cases hs : s < n
    · have hlt : b*s+i < b*n := by nlinarith
      simp [testBit_lane, hi, hs, hlt]
    · have hge : b*n ≤ b*s+i := by nlinarith
      simp [testBit_lane, hi, hs, Nat.not_lt_of_ge hge]
  · simp only [testBit_lane, hi, decide_false, Bool.false_and]
    split <;> simp [testBit_lane, hi]

theorem lane_moveDown (P b w s : Nat) (hb : 0 < b) :
    lane (moveDown P b w) b s =
      if s < w*w ∧ w ≤ s then lane P b (s-w) else 0 := by
  rw [moveDown, lane_truncate _ _ _ _ hb, lane_shiftLeft _ _ _ _ hb]
  split_ifs <;> simp_all

theorem lane_moveUp (P b w s : Nat) (hb : 0 < b) :
    lane (moveUp P b w) b s = if s < w*w then lane P b (s+w) else 0 := by
  rw [moveUp, lane_truncate _ _ _ _ hb, lane_shiftRight]

theorem lane_rowMask (P b w r s : Nat) :
    lane (Nat.land P (rowMask b w r)) b s =
      if s < w*w ∧ s / w = r then lane P b s else 0 := by
  unfold rowMask
  rw [lane_mask]
  simp

theorem lane_columnMask (P b w c s : Nat) :
    lane (Nat.land P (columnMask b w c)) b s =
      if s < w*w ∧ s % w = c then lane P b s else 0 := by
  unfold columnMask
  rw [lane_mask]
  simp

#print axioms lane_truncate
#print axioms lane_moveDown
#print axioms lane_moveUp
#print axioms lane_rowMask
#print axioms lane_columnMask
#print axioms testBit_lane
#print axioms lane_land
#print axioms lane_shiftRight
#print axioms lane_shiftLeft
#print axioms lane_laneMask
#print axioms lane_mask
#print axioms lane_moveRight
#print axioms lane_moveLeft
end AKLT.Gen.Packed
