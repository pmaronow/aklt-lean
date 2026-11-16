import Mathlib

/-! Packed nonnegative integers, with least significant lane first. -/
namespace AKLT.Gen.Packed

/-- Extract lane `s` of width `b`. -/
def lane (P b s : Nat) : Nat := (P >>> (b * s)) % 2 ^ b

/-- Pack `n` lanes supplied by a function. Out-of-range values are ignored. -/
def packFn (b : Nat) : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | n + 1, f => f 0 + 2 ^ b * packFn b n (fun s => f (s + 1))

/-- Pack a list, least significant lane first. -/
def pack (b : Nat) : List Nat → Nat
  | [] => 0
  | a :: as => a + 2 ^ b * pack b as

/-- All stored bits lie in the first `n` lanes. -/
def Fits (P b n : Nat) : Prop := P < 2 ^ (b * n)

@[simp] theorem lane_zero (P b : Nat) : lane P b 0 = P % 2 ^ b := by
  simp [lane]

@[simp] theorem lane_succ (P b s : Nat) :
    lane P b (s + 1) = lane (P / 2 ^ b) b s := by
  simp only [lane, Nat.shiftRight_eq_div_pow, Nat.mul_add, Nat.mul_one,
    pow_add, Nat.div_div_eq_div_mul]
  rw [Nat.mul_comm (2 ^ (b * s)) (2 ^ b)]

@[simp] theorem lane_lt (P b s : Nat) : lane P b s < 2 ^ b :=
  Nat.mod_lt _ (by positivity)

private theorem head_mod (b a q : Nat) (ha : a < 2 ^ b) :
    (a + 2 ^ b * q) % 2 ^ b = a := by simp [Nat.add_mod, Nat.mod_eq_of_lt ha]

private theorem head_div (b a q : Nat) (ha : a < 2 ^ b) :
    (a + 2 ^ b * q) / 2 ^ b = q := by
  rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt ha, Nat.zero_add]

theorem lane_packFn (b n : Nat) (f : Nat → Nat)
    (hf : ∀ s < n, f s < 2 ^ b) (s : Nat) :
    lane (packFn b n f) b s = if s < n then f s else 0 := by
  induction n generalizing f s with
  | zero => simp [packFn, lane]
  | succ n ih =>
    cases s with
    | zero => simp [packFn, head_mod b _ _ (hf 0 (by omega))]
    | succ s =>
      rw [lane_succ, packFn, head_div b _ _ (hf 0 (by omega)),
        ih _ (fun i hi => hf (i + 1) (by omega))]
      simp only [Nat.add_lt_add_iff_right]

theorem packFn_lt (b n : Nat) (f : Nat → Nat)
    (hf : ∀ s < n, f s < 2 ^ b) : Fits (packFn b n f) b n := by
  induction n generalizing f with
  | zero => simp [packFn, Fits]
  | succ n ih =>
    have h := ih (fun i => f (i+1)) (fun i hi => hf (i+1) (by omega))
    have h0 := hf 0 (by omega)
    dsimp [Fits] at *
    simp only [packFn, Nat.mul_add, Nat.mul_one, pow_add]
    have hp : 0 < 2 ^ b := by positivity
    nlinarith

theorem packFn_lanes (P b n : Nat) (hP : Fits P b n) :
    packFn b n (lane P b) = P := by
  induction n generalizing P with
  | zero => simpa [Fits, packFn] using (show P = 0 by simpa [Fits] using hP).symm
  | succ n ih =>
    have hq : Fits (P / 2 ^ b) b n := by
      dsimp [Fits] at *
      apply (Nat.div_lt_iff_lt_mul (by positivity)).2
      simpa [Nat.mul_add, pow_add, Nat.mul_comm] using hP
    simp only [packFn, lane_zero, lane_succ, ih _ hq]
    exact Nat.mod_add_div P (2 ^ b)

theorem lane_eq_zero_of_fits {P b n : Nat} (hP : Fits P b n) (s : Nat) (hs : n ≤ s) :
    lane P b s = 0 := by
  dsimp [lane]
  rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt, Nat.zero_mod]
  exact lt_of_lt_of_le hP (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left b hs))

theorem lanes_ext {P Q b n : Nat} (hP : Fits P b n) (hQ : Fits Q b n)
    (h : ∀ s < n, lane P b s = lane Q b s) : P = Q := by
  rw [← packFn_lanes P b n hP, ← packFn_lanes Q b n hQ]
  congr 1
  funext s
  by_cases hs : s < n
  · exact h s hs
  · have zero_lane (R : Nat) (hR : Fits R b n) : lane R b s = 0 := by
      dsimp [lane]
      rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt, Nat.zero_mod]
      exact lt_of_lt_of_le hR (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left b (by omega)))
    rw [zero_lane P hP, zero_lane Q hQ]

theorem packFn_add (b n : Nat) (f g : Nat → Nat) :
    packFn b n (fun s => f s + g s) = packFn b n f + packFn b n g := by
  induction n generalizing f g with
  | zero => simp [packFn]
  | succ n ih => simp only [packFn, ih]; ring

theorem packFn_mul (b n c : Nat) (f : Nat → Nat) :
    packFn b n (fun s => c * f s) = c * packFn b n f := by
  induction n generalizing f with
  | zero => simp [packFn]
  | succ n ih => simp only [packFn, ih]; ring

/-- Addition without carries, from explicit bounds on every input lane sum. -/
theorem lane_add {P Q b n : Nat} (hP : Fits P b n) (hQ : Fits Q b n)
    (h : ∀ s < n, lane P b s + lane Q b s < 2 ^ b) (s : Nat) (hs : s < n) :
    lane (P + Q) b s = lane P b s + lane Q b s := by
  rw [← packFn_lanes P b n hP, ← packFn_lanes Q b n hQ, ← packFn_add]
  rw [lane_packFn b n _ (by simpa [packFn_lanes P b n hP, packFn_lanes Q b n hQ] using h) s,
    ite_eq_left hs, packFn_lanes P b n hP, packFn_lanes Q b n hQ]

/-- Scalar multiplication without carries. -/
theorem lane_mul {P b n c : Nat} (hP : Fits P b n)
    (h : ∀ s < n, c * lane P b s < 2 ^ b) (s : Nat) (hs : s < n) :
    lane (c * P) b s = c * lane P b s := by
  rw [← packFn_lanes P b n hP, ← packFn_mul]
  rw [lane_packFn b n _ (by simpa [packFn_lanes P b n hP] using h) s,
    ite_eq_left hs, packFn_lanes P b n hP]

theorem packFn_congr (b n : Nat) (f g : Nat → Nat)
    (h : ∀ s < n, f s = g s) : packFn b n f = packFn b n g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    simp only [packFn, h 0 (by omega), ih _ _ (fun i hi => h (i+1) (by omega))]

/-- `pack` is the function packer applied to the list with zero default. -/
theorem pack_eq_packFn (b : Nat) (xs : List Nat) :
    pack b xs = packFn b xs.length (fun s => xs[s]?.getD 0) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simpa [pack, packFn] using congrArg (fun q => a + 2 ^ b * q) ih

theorem lane_pack (b : Nat) (xs : List Nat)
    (h : ∀ a ∈ xs, a < 2 ^ b) (s : Nat) :
    lane (pack b xs) b s = xs[s]?.getD 0 := by
  rw [pack_eq_packFn, lane_packFn]
  · split_ifs with hs
    · rfl
    · have hn : xs[s]? = none := List.getElem?_eq_none (by omega)
      simp [hn]
  · intro i hi
    rw [List.getElem?_eq_getElem hi]
    exact h _ (List.getElem_mem hi)

/-- Closed-form constant plane, evaluated using a few large natural operations. -/
def repeatLane (b n v : Nat) : Nat := (2 ^ (b * n) - 1) * v / (2 ^ b - 1)

theorem repeatLane_eq (b n v : Nat) (hb : 0 < b) :
    repeatLane b n v = packFn b n (fun _ => v) := by
  have hbase : 1 < 2 ^ b := Nat.one_lt_pow (by omega) (by decide)
  have hmul : ∀ n, (2 ^ b - 1) * packFn b n (fun _ => v) =
      (2 ^ (b * n) - 1) * v := by
    intro n
    induction n with
    | zero => simp [packFn]
    | succ n ih =>
      have hp : 0 < 2 ^ (b*n) := by positivity
      simp only [packFn, Nat.mul_add, Nat.mul_one, pow_add]
      have h1 := Nat.sub_add_cancel (show 1 ≤ 2 ^ b by omega)
      have h2 := Nat.sub_add_cancel (show 1 ≤ 2 ^ (b*n) by omega)
      have h3 := Nat.sub_add_cancel (show 1 ≤ 2 ^ (b*n) * 2 ^ b by nlinarith)
      calc
        (2 ^ b - 1) * v + (2 ^ b - 1) * (2 ^ b * packFn b n (fun _ => v)) =
            (2 ^ b - 1) * v + 2 ^ b * ((2 ^ b - 1) * packFn b n (fun _ => v)) := by ring
        _ = ((2 ^ b - 1) + 2 ^ b * (2 ^ (b*n) - 1)) * v := by rw [ih]; ring
        _ = (2 ^ (b*n) * 2 ^ b - 1) * v := by congr 1; nlinarith

  exact (Nat.eq_div_of_mul_eq_right (by omega) (hmul n)).symm

#print axioms packFn_congr
#print axioms pack_eq_packFn
#print axioms lane_pack
#print axioms repeatLane_eq
#print axioms lane_zero
#print axioms lane_succ
#print axioms lane_lt
#print axioms lane_packFn
#print axioms packFn_lt
#print axioms packFn_lanes
#print axioms lane_eq_zero_of_fits
#print axioms lanes_ext
#print axioms packFn_add
#print axioms packFn_mul
#print axioms lane_add
#print axioms lane_mul
end AKLT.Gen.Packed
