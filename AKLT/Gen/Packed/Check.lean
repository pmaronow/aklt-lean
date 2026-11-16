import AKLT.Gen.Packed.Guard
namespace AKLT.Gen.Packed

/-- A repeated low-bit cap, with a GMP-friendly closed-form mask. -/
def capMask (b n k : Nat) : Nat := repeatLane b n (2^k-1)
def capCheck (b n k P : Nat) : Bool := Nat.land P (capMask b n k) == P

theorem capCheck_sound {P b n k : Nat} (hb : 0 < b) (hk : k ≤ b)
    (h : capCheck b n k P = true) : Fits P b n ∧ ∀ s < n, lane P b s < 2^k := by
  have hv : 2^k-1 < 2^b := by
    have hp : 0 < 2^k := by positivity
    have := Nat.pow_le_pow_right (by decide : 0 < 2) hk
    omega
  have he : Nat.land P (capMask b n k) = P := by simpa [capCheck] using h
  have hcap : Fits (capMask b n k) b n := by
    rw [capMask, repeatLane_eq _ _ _ hb]
    exact packFn_lt _ _ _ (fun _ _ => hv)
  constructor
  · rw [← he]
    exact lt_of_le_of_lt Nat.and_le_right hcap
  · intro s hs
    have hmask : lane (capMask b n k) b s = 2^k-1 := by
      rw [capMask, repeatLane_eq _ _ _ hb, lane_packFn _ _ _ (fun _ _ => hv)]
      simp [hs]
    have hl := congrArg (fun Q => lane Q b s) he
    rw [lane_land, hmask] at hl
    have hle : lane P b s ≤ 2^k-1 := by rw [← hl]; exact Nat.and_le_right
    have : 0 < 2^k := by positivity
    omega

/-- Two-term row: the first term reads the next lane, with zero fill. -/
def linearRHS (B b c₁ c₂ : Nat) : Nat := c₁ * (B >>> b) + c₂ * B

theorem linearRHS_pack {B b n : Nat} (hB : Fits B b n) (c₁ c₂ : Nat) :
    linearRHS B b c₁ c₂ =
      packFn b n (fun s => c₁ * lane B b (s+1) + c₂ * lane B b s) := by
  have hshift : Fits (B >>> b) b n := lt_of_le_of_lt (Nat.shiftRight_le _ _) hB
  unfold linearRHS
  conv_lhs => rw [← packFn_lanes (B >>> b) b n hshift, ← packFn_lanes B b n hB]
  rw [← packFn_mul, ← packFn_mul, ← packFn_add]
  apply packFn_congr
  intro s hs
  have he : lane (B >>> b) b s = lane B b (s+1) := by
    simpa only [Nat.mul_one] using lane_shiftRight B b 1 s
  rw [packFn_lanes B b n hB, he]

/-- This checker checks both input caps, the coefficient size, and the row.
Its cost uses whole-plane operations, without a scalar lane traversal. -/
def rowCheck (g n k c₁ c₂ A B : Nat) : Bool :=
  decide (k ≤ g) && decide ((c₁+c₂)*2^k < 2^g) &&
  capCheck (g+1) n k A && capCheck (g+1) n k B &&
  guardCheck g n A (linearRHS B (g+1) c₁ c₂)

/-- The Boolean row checker proves the mathematical inequality at every lane,
including the zero-filled part beyond the finite plane. -/
theorem rowCheck_sound {g n k c₁ c₂ A B : Nat}
    (h : rowCheck g n k c₁ c₂ A B = true) :
    ∀ s, lane A (g+1) s ≤ c₁ * lane B (g+1) (s+1) + c₂ * lane B (g+1) s := by
  simp only [rowCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨⟨hk, hc⟩, ha⟩, hb⟩, hguard⟩
  obtain ⟨hA, hla⟩ := capCheck_sound (by omega : 0 < g+1) (by omega : k ≤ g+1) ha
  obtain ⟨hB, hlb⟩ := capCheck_sound (by omega : 0 < g+1) (by omega : k ≤ g+1) hb
  have hpow : 2^k ≤ 2^g := Nat.pow_le_pow_right (by decide) hk
  have hd : ∀ s < n, c₁ * lane B (g+1) (s+1) + c₂ * lane B (g+1) s < 2^g := by
    intro s hs
    have h0 := hlb s hs
    have h1 : lane B (g+1) (s+1) < 2^k := by
      by_cases hsn : s+1 < n
      · exact hlb (s+1) hsn
      · rw [lane_eq_zero_of_fits hB _ (by omega)]; positivity
    nlinarith
  have hd' : ∀ s < n, c₁ * lane B (g+1) (s+1) + c₂ * lane B (g+1) s < 2^(g+1) := by
    intro s hs
    have hp : 0 < 2^g := by positivity
    exact lt_trans (hd s hs) (by rw [pow_succ]; omega)
  have hrhs : Fits (linearRHS B (g+1) c₁ c₂) (g+1) n := by
    rw [linearRHS_pack hB]
    exact packFn_lt _ _ _ hd'
  have hrl : ∀ s < n, lane (linearRHS B (g+1) c₁ c₂) (g+1) s =
      c₁ * lane B (g+1) (s+1) + c₂ * lane B (g+1) s := by
    intro s hs
    rw [linearRHS_pack hB, lane_packFn _ _ _ hd', ite_eq_left hs]
  have hh := (guardCheck_iff hA hrhs (fun s hs => lt_of_lt_of_le (hla s hs) hpow)
    (fun s hs => by rw [hrl s hs]; exact hd s hs)).1 hguard
  intro s
  by_cases hs : s < n
  · simpa [hrl s hs] using hh s hs
  · rw [lane_eq_zero_of_fits hA _ (by omega)]; omega

/-- Successive rows use successively shifted pairs of planes. -/
def rowsCheck (g n k c₁ c₂ : Nat) : Nat → Nat → Nat → Bool
  | 0, _, _ => true
  | r+1, A, B => rowCheck g n k c₁ c₂ A B && rowsCheck g n k c₁ c₂ r (A >>> (g+1)) (B >>> (g+1))

theorem rowsCheck_sound {g n k c₁ c₂ r A B : Nat}
    (h : rowsCheck g n k c₁ c₂ r A B = true) (j : Nat) (hj : j < r) :
    ∀ s, lane A (g+1) (s+j) ≤
      c₁ * lane B (g+1) (s+j+1) + c₂ * lane B (g+1) (s+j) := by
  induction r generalizing A B j with
  | zero => omega
  | succ r ih =>
    simp only [rowsCheck, Bool.and_eq_true] at h
    cases j with
    | zero => simpa using rowCheck_sound h.1
    | succ j =>
      have hh := ih h.2 j (by omega)
      intro s
      have he := hh s
      have heq (Q t : Nat) : lane (Q >>> (g+1)) (g+1) t = lane Q (g+1) (t+1) := by
        simpa only [Nat.mul_one] using lane_shiftRight Q (g+1) 1 t
      simpa only [heq, Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using he

#print axioms capCheck_sound
#print axioms linearRHS_pack
#print axioms rowCheck_sound
#print axioms rowsCheck_sound
end AKLT.Gen.Packed
