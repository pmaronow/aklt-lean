module
public import AKLT.Gen.Packed.Routing

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true
namespace AKLT.Gen.Packed

/-- Guard bit `g` in each field of width `g+1`. -/
def guardMask (g n : Nat) : Nat := repeatLane (g+1) n (2^g)

private theorem guard_digit_lt (g : Nat) : 2^g < 2^(g+1) := by
  rw [pow_succ]
  have hp : 0 < 2^g := by positivity
  omega

theorem lane_guardMask (g n s : Nat) (hs : s < n) :
    lane (guardMask g n) (g+1) s = 2^g := by
  rw [guardMask, repeatLane_eq _ _ _ (by omega), lane_packFn]
  · simp [hs]
  · exact fun _ _ => guard_digit_lt g

theorem guardMask_fits (g n : Nat) : Fits (guardMask g n) (g+1) n := by
  rw [guardMask, repeatLane_eq _ _ _ (by omega)]
  exact packFn_lt _ _ _ (fun _ _ => guard_digit_lt g)

private theorem highBit_iff (d g : Nat) (hd : d < 2^(g+1)) :
    Nat.land d (2^g) = 2^g ↔ 2^g ≤ d := by
  rw [Nat.land_eq, Nat.and_two_pow]
  constructor
  · intro h
    by_contra hn
    have ht := Nat.testBit_lt_two_pow (show d < 2^g by omega)
    simp [ht] at h
    have : 0 < 2^g := by positivity
    omega
  · intro h
    simp [Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt h hd]

/-- The guard prevents inter-lane borrowing. The result has digits
`2^g + B_s - A_s`, strictly below the field base. -/
theorem lane_guard_sub {A B g n : Nat} (hA : Fits A (g+1) n) (hB : Fits B (g+1) n)
    (ha : ∀ s < n, lane A (g+1) s < 2^g)
    (hb : ∀ s < n, lane B (g+1) s < 2^g) (s : Nat) (hs : s < n) :
    lane (guardMask g n + B - A) (g+1) s =
      2^g + lane B (g+1) s - lane A (g+1) s := by
  let d := fun i => 2^g + lane B (g+1) i - lane A (g+1) i
  have hd : ∀ i < n, d i < 2^(g+1) := by
    intro i hi
    have := hb i hi
    dsimp [d]
    rw [pow_succ]
    omega
  have he : packFn (g+1) n d + A = guardMask g n + B := by
    rw [← packFn_lanes A (g+1) n hA, ← packFn_add,
      guardMask, repeatLane_eq _ _ _ (by omega),
      ← packFn_lanes B (g+1) n hB, ← packFn_add]
    apply packFn_congr
    intro i hi
    have := ha i hi
    dsimp [d]
    omega
  have he' : guardMask g n + B - A = packFn (g+1) n d := by omega
  rw [he', lane_packFn _ _ _ hd, ite_eq_left hs]

/-- A single masked guarded subtraction is equivalent to all component
comparisons. Both operands must fit, and each lane must be below the guard. -/
theorem guard_compare {A B g n : Nat} (hA : Fits A (g+1) n) (hB : Fits B (g+1) n)
    (ha : ∀ s < n, lane A (g+1) s < 2^g)
    (hb : ∀ s < n, lane B (g+1) s < 2^g) :
    Nat.land (guardMask g n + B - A) (guardMask g n) = guardMask g n ↔
      ∀ s < n, lane A (g+1) s ≤ lane B (g+1) s := by
  have hd (s : Nat) (hs : s < n) :
      2^g + lane B (g+1) s - lane A (g+1) s < 2^(g+1) := by
    have := hb s hs
    rw [pow_succ]
    omega
  constructor
  · intro h s hs
    have he := congrArg (fun P => lane P (g+1) s) h
    rw [lane_land, lane_guardMask _ _ _ hs, lane_guard_sub hA hB ha hb s hs] at he
    have := (highBit_iff _ g (hd s hs)).1 he
    have := ha s hs
    omega
  · intro h
    apply lanes_ext (n := n)
    · exact lt_of_le_of_lt Nat.and_le_right (guardMask_fits g n)
    · exact guardMask_fits g n
    · intro s hs
      rw [lane_land, lane_guardMask _ _ _ hs, lane_guard_sub hA hB ha hb s hs]
      apply (highBit_iff _ g (hd s hs)).2
      have := h s hs
      omega

/-- Unbounded-index form: all lanes beyond `n` are zero by `Fits`. -/
theorem guard_compare_all {A B g n : Nat} (hA : Fits A (g+1) n) (hB : Fits B (g+1) n)
    (ha : ∀ s < n, lane A (g+1) s < 2^g)
    (hb : ∀ s < n, lane B (g+1) s < 2^g) :
    Nat.land (guardMask g n + B - A) (guardMask g n) = guardMask g n ↔
      ∀ s, lane A (g+1) s ≤ lane B (g+1) s := by
  rw [guard_compare hA hB ha hb]
  constructor
  · intro h s
    by_cases hs : s < n
    · exact h s hs
    · rw [lane_eq_zero_of_fits hA s (by omega)]
      omega
  · intro h s hs
    exact h s

def guardCheck (g n A B : Nat) : Bool :=
  Nat.land (guardMask g n + B - A) (guardMask g n) == guardMask g n

theorem guardCheck_iff {A B g n : Nat} (hA : Fits A (g+1) n) (hB : Fits B (g+1) n)
    (ha : ∀ s < n, lane A (g+1) s < 2^g)
    (hb : ∀ s < n, lane B (g+1) s < 2^g) :
    guardCheck g n A B = true ↔ ∀ s < n, lane A (g+1) s ≤ lane B (g+1) s := by
  simpa [guardCheck] using guard_compare hA hB ha hb

#print axioms lane_guardMask
#print axioms guardMask_fits
#print axioms lane_guard_sub
#print axioms guard_compare
#print axioms guard_compare_all
#print axioms guardCheck_iff
end AKLT.Gen.Packed
