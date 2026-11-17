module
public import AKLT.Gen.Packed.Basic

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true
namespace AKLT.Gen.Packed

/-- Recursive packing agrees with the usual base-two plane sum. -/
theorem packFn_eq_sum (b n : Nat) (f : Nat → Nat) :
    packFn b n f = ∑ s ∈ Finset.range n, f s * 2^(b*s) := by
  induction n generalizing f with
  | zero => simp [packFn]
  | succ n ih =>
    rw [packFn, ih, Finset.sum_range_succ']
    simp only [Nat.mul_zero, pow_zero, Nat.mul_one]
    rw [Finset.mul_sum]
    have he : (∑ s ∈ Finset.range n, 2^b * (f (s+1) * 2^(b*s))) =
        ∑ s ∈ Finset.range n, f (s+1) * 2^(b*(s+1)) := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [Nat.mul_add, Nat.mul_one, pow_add]
      ring
    rw [he, Nat.add_comm]

/-- Concatenating lane lists is a shift-and-add operation. This also supports
literal chunking without a trusted loader. -/
theorem pack_append (b : Nat) (xs ys : List Nat) :
    pack b (xs ++ ys) = pack b xs + 2^(b*xs.length) * pack b ys := by
  induction xs with
  | nil => simp [pack]
  | cons a xs ih =>
    simp only [List.cons_append, pack, ih, List.length_cons, Nat.mul_add,
      Nat.mul_one, pow_add]
    ring

#print axioms packFn_eq_sum
#print axioms pack_append
end AKLT.Gen.Packed
