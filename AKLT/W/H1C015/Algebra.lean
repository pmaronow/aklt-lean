module
public import AKLT.Cert.H1.Production.Leaves
public import Mathlib.NumberTheory.Zsqrtd.Basic

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

namespace AKLT.W.H1C015

open AKLT.Cert.H1 AKLT.Cert.H1.Production
open scoped BigOperators

/-- Both integer components, in the usual Gaussian integer ring. -/
abbrev R := Zsqrtd (-1)

def value (a : Gaussian) : R := ⟨a.re, a.im⟩

theorem value_injective : Function.Injective value := by
  intro a b h
  cases a; cases b
  have hr := congrArg Zsqrtd.re h
  have hi := congrArg Zsqrtd.im h
  simp only [value] at hr hi
  cases hr
  cases hi
  rfl

@[simp] theorem value_zero : value Gaussian.zero = 0 := rfl
@[simp] theorem value_one : value Gaussian.one = 1 := rfl
@[simp] theorem value_add (a b : Gaussian) : value (a.add b) = value a + value b := rfl

@[simp] theorem value_scale (n : Int) (a : Gaussian) :
    value (a.scale n) = (n : R) * value a := by
  apply Zsqrtd.ext <;> simp [value, Gaussian.scale]

lemma gaussian_beq_zero_eq (a : Gaussian) (h : a == Gaussian.zero) : a = Gaussian.zero := by
  cases a with
  | mk re im =>
      change (re == 0 && im == 0) = true at h
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      rcases h with ⟨hr, hi⟩
      subst re
      subst im
      rfl

lemma gaussian_mul_raw (a b : Gaussian) :
    a.mul b = ⟨a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re⟩ := by
  by_cases h : a == Gaussian.zero || b == Gaussian.zero
  · have hz : a = Gaussian.zero ∨ b = Gaussian.zero := by
      rcases Bool.or_eq_true_iff.mp h with ha | hb
      · exact Or.inl (gaussian_beq_zero_eq a ha)
      · exact Or.inr (gaussian_beq_zero_eq b hb)
    rcases hz with ha | hb
    · subst a
      simp [Gaussian.mul, Gaussian.zero]
    · subst b
      simp [Gaussian.mul, Gaussian.zero]
  · simp [Gaussian.mul, h]

@[simp] theorem value_mul (a b : Gaussian) : value (a.mul b) = value a * value b := by
  rw [gaussian_mul_raw]
  apply Zsqrtd.ext <;> simp [value, sub_eq_add_neg]

@[simp] theorem value_sum (xs : List Gaussian) :
    value (sumGaussian xs) = (xs.map value).sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [sumGaussian, value_add, List.map_cons, List.sum_cons, ih]

theorem sum_list_range {S : Type*} [AddCommMonoid S] (n : Nat) (f : Nat → S) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.sum_range_succ, Finset.sum_range_succ, ih]

@[simp] theorem value_sum_range (n : Nat) (f : Nat → Gaussian) :
    value (sumGaussian ((List.range n).map f)) =
      ∑ i ∈ Finset.range n, value (f i) := by
  rw [value_sum, List.map_map]
  exact sum_list_range n _

theorem sum_blocks {S : Type*} [AddCommMonoid S] (m n : Nat) (f : Nat → S) :
    (∑ c ∈ Finset.range (m*n), f c) =
      ∑ a ∈ Finset.range m, ∑ b ∈ Finset.range n, f (a*n+b) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Nat.succ_mul, Finset.sum_range_add, Finset.sum_range_succ, ih]

theorem getD_map_range {S : Type*} (n : Nat) (f : Nat → S) (d : S)
    (i : Nat) (hi : i < n) : ((List.range n).map f).getD i d = f i := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp only [List.getElem_map, List.getElem_range]

theorem matrixEntry_map (f : Nat → Nat → Gaussian) (i j : Nat)
    (hi : i < 4) (hj : j < 4) :
    matrixEntry ((List.range 4).map fun l => (List.range 4).map (f l)) i j = f i j := by
  unfold matrixEntry
  rw [getD_map_range 4 _ [] i hi, getD_map_range 4 _ Gaussian.zero j hj]

def entry (m : FourMatrix) (i j : Nat) : R := value (matrixEntry m i j)

theorem entry_mul (a b : FourMatrix) (i j : Nat) (hi : i < 4) (hj : j < 4) :
    entry (fourMul a b) i j =
      ∑ k ∈ Finset.range 4, entry a i k * entry b k j := by
  unfold entry fourMul
  rw [matrixEntry_map _ i j hi hj, value_sum_range]
  simp only [value_mul]

@[simp] theorem value_trace (m : FourMatrix) :
    value (fourTrace m) = ∑ i ∈ Finset.range 4, entry m i i := by
  exact value_sum_range 4 _

/-- A scalar monomial at the packing base. -/
def weight (width col : Nat) : R := (2 : R) ^ (width*col)

@[simp] theorem weight_zero (width : Nat) : weight width 0 = 1 := by
  simp [weight]

theorem weight_add (width a b : Nat) :
    weight width (a+b) = weight width a * weight width b := by
  simp only [weight, Nat.mul_add, pow_add]

theorem weight_pow (width stride digit : Nat) :
    (weight width stride)^digit = weight width (digit*stride) := by
  simp only [weight, ← pow_mul]
  congr 1
  ring

theorem value_pack_map {S : Type*} (base : Int) (xs : List S) (f : S → Gaussian)
    (d : S) :
    value (packGaussian base (xs.map f)) =
      ∑ i ∈ Finset.range xs.length, value (f (xs.getD i d)) * (base : R)^i := by
  induction xs with
  | nil => simp [packGaussian]
  | cons a xs ih =>
      simp only [List.map_cons, packGaussian, value_add, value_scale, List.length_cons]
      rw [Finset.sum_range_succ', ih, Finset.mul_sum]
      simp only [List.getD_cons_zero, pow_zero, mul_one, List.getD_cons_succ, pow_succ]
      rw [add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      ring

end AKLT.W.H1C015
