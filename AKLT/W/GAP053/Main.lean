import AKLT.Blueprint.Gap.NodesShell

open AKLT.Blueprint.Gap

namespace AKLT.W.GAP053

theorem main : AKLT.Blueprint.Gap.BinomialTailStatement := by
  intro d hd0 hdhalf n hn
  let r : ℕ := n - 3
  have hrbaseNat : r + 1 - 20 = n - 22 := by
    dsimp [r]
    omega
  have hbaseReal : (n : ℝ) / 2 ≤ ((r + 1 - 20 : ℕ) : ℝ) := by
    rw [hrbaseNat, Nat.cast_sub (by omega : 22 ≤ n)]
    have hnreal : (44 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hfact : 0 < (Nat.factorial 20 : ℝ) := by exact_mod_cast Nat.factorial_pos 20
  have hchooseLower : ((n : ℝ) / 2) ^ 20 / (Nat.factorial 20 : ℝ) ≤
      (Nat.choose r 20 : ℝ) := by
    have hchoose := Nat.pow_le_choose (α := ℝ) 20 r
    calc
      ((n : ℝ) / 2) ^ 20 / (Nat.factorial 20 : ℝ) ≤
          (((r + 1 - 20 : ℕ) : ℝ) ^ 20) / (Nat.factorial 20 : ℝ) := by
        gcongr
      _ ≤ (Nat.choose r 20 : ℝ) := hchoose
  have hsumEq : (1 + d) ^ r =
      ∑ k ∈ Finset.range (r + 1),
        d ^ k * (1 : ℝ) ^ (r - k) * (Nat.choose r k : ℝ) := by
    rw [show 1 + d = d + 1 by ring, add_pow]
  have hmem : 20 ∈ Finset.range (r + 1) := by
    apply Finset.mem_range.mpr
    dsimp [r]
    omega
  have hbin : d ^ 20 * (Nat.choose r 20 : ℝ) ≤ (1 + d) ^ r := by
    rw [hsumEq]
    have h := Finset.single_le_sum
      (s := Finset.range (r + 1))
      (f := fun k => d ^ k * (1 : ℝ) ^ (r - k) * (Nat.choose r k : ℝ))
      (fun k hk => mul_nonneg
        (mul_nonneg (pow_nonneg hd0.le _) (pow_nonneg (show 0 ≤ (1 : ℝ) by norm_num) _))
        (Nat.cast_nonneg _))
      hmem
    simpa using h
  let C : ℝ := d ^ 20 * (((n : ℝ) / 2) ^ 20 / (Nat.factorial 20 : ℝ))
  have hC : C ≤ (1 + d) ^ r := by
    dsimp [C]
    exact (mul_le_mul_of_nonneg_left hchooseLower (pow_nonneg hd0.le _)).trans hbin
  have hd1 : d ≤ 1 := by linarith
  have hbase0 : 0 ≤ (1 - d) * (1 + d) :=
    mul_nonneg (sub_nonneg.mpr hd1) (by positivity)
  have hbase1 : (1 - d) * (1 + d) ≤ 1 := by
    nlinarith [sq_nonneg d]
  have hpowprod : (1 - d) ^ r * (1 + d) ^ r ≤ 1 := by
    rw [← mul_pow]
    exact pow_le_one₀ hbase0 hbase1
  have hprod : (1 - d) ^ r * C ≤ 1 := by
    calc
      (1 - d) ^ r * C ≤ (1 - d) ^ r * (1 + d) ^ r :=
        mul_le_mul_of_nonneg_left hC (pow_nonneg (sub_nonneg.mpr hd1) _)
      _ ≤ 1 := hpowprod
  have hfactor : C * (2 ^ 20 * (Nat.factorial 20 : ℝ)) = d ^ 20 * (n : ℝ) ^ 20 := by
    dsimp [C]
    have hf : (Nat.factorial 20 : ℝ) ≠ 0 := ne_of_gt hfact
    field_simp
  have hden : 0 < d ^ 20 * (n : ℝ) ^ 20 := by
    apply mul_pos
    · exact pow_pos hd0 _
    · exact pow_pos (by exact_mod_cast (show 0 < n by omega)) _
  rw [le_div_iff₀ hden]
  calc
    (1 - d) ^ r * (d ^ 20 * (n : ℝ) ^ 20) =
        ((1 - d) ^ r * C) * (2 ^ 20 * (Nat.factorial 20 : ℝ)) := by
          rw [← hfactor]
          ring
    _ ≤ 1 * (2 ^ 20 * (Nat.factorial 20 : ℝ)) :=
      mul_le_mul_of_nonneg_right hprod (by positivity)
    _ = 2 ^ 20 * (Nat.factorial 20 : ℝ) := by ring

#print axioms main

end AKLT.W.GAP053
