module
public import AKLT.W.REC072.Estimates

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators ENNReal
open AKLT.Defs AKLT.Blueprint.Rec

namespace AKLT.W.REC072

/-- The coarse H2 bound remains summable after counting the possible shifts. -/
lemma lengthRowMajorant_summable {CV q : ℝ} (hbound : OpenTrailBound CV q) :
    Summable (fun n : ℕ => (n + 2 : ℝ) * (6 * n) * CV * q ^ n) := by
  have hnorm : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hbound.2.1]
    exact hbound.2.2.1
  have hquadratic := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 2 hnorm
  have hlinear := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hnorm
  exact ((hquadratic.add (hlinear.mul_left 2)).mul_left (6 * CV)).congr
    (fun n => by simp only [pow_one]; ring)

/-- A length has at most n+2 possible shifts, each bounded using H2. -/
lemma coefficient_length_sum_le {CV q : ℝ} (hbound : OpenTrailBound CV q)
    (X Y : PairType) (n : ℕ) :
    (∑' s : ℕ, ENNReal.ofReal (kernelLengthCoefficient X Y s n : ℝ)) ≤
      ENNReal.ofReal ((n + 2 : ℝ) * (6 * n) * CV * q ^ n) := by
  classical
  rw [tsum_eq_sum (s := Finset.range (n + 2)) (fun s hs => by
    have hs' : n + 1 < s := by
      simp only [Finset.mem_range] at hs
      omega
    rw [kernelLengthCoefficient_zero_of_shift_large X Y n s hs']
    simp)]
  rw [← ENNReal.ofReal_sum_of_nonneg (by
    intro s hs
    exact_mod_cast kernelLengthCoefficient_nonneg X Y s n)]
  apply ENNReal.ofReal_le_ofReal
  calc
    (∑ s ∈ Finset.range (n + 2), (kernelLengthCoefficient X Y s n : ℝ)) ≤
        ∑ _s ∈ Finset.range (n + 2), (6 * n : ℝ) * CV * q ^ n :=
      Finset.sum_le_sum fun s _ => kernelLengthCoefficient_bound hbound X Y s n
    _ = (n + 2 : ℝ) * (6 * n) * CV * q ^ n := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add,
        Nat.cast_ofNat]
      ring

/-- Regroup nonnegative length and shift sums before converting them to reals. -/
lemma shiftKernel_row_ne_top {CV q : ℝ} (hbound : OpenTrailBound CV q)
    (X Y : PairType) : (∑' s : ℕ, shiftKernel X Y s) ≠ ⊤ := by
  have hmajorant : (∑' n : ℕ,
      ENNReal.ofReal ((n + 2 : ℝ) * (6 * n) * CV * q ^ n)) ≠ ⊤ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (by
      intro n
      have hCV : 0 ≤ CV := le_trans (by norm_num) hbound.1
      have hq : 0 ≤ q := hbound.2.1.le
      positivity) (lengthRowMajorant_summable hbound)]
    exact ENNReal.ofReal_ne_top
  apply ne_top_of_le_ne_top hmajorant
  calc
    (∑' s : ℕ, shiftKernel X Y s) =
        ∑' n : ℕ, ∑' s : ℕ,
          ENNReal.ofReal (kernelLengthCoefficient X Y s n : ℝ) :=
      ENNReal.tsum_comm
    _ ≤ ∑' n : ℕ, ENNReal.ofReal ((n + 2 : ℝ) * (6 * n) * CV * q ^ n) :=
      ENNReal.tsum_le_tsum (coefficient_length_sum_le hbound X Y)

/-- H2 supplies the analytic bridge required by the finite cutoff comparison. -/
theorem kernelSeriesBridge : ResidualKernelSeriesBridge := by
  classical
  intro CV q hbound X
  have hshift (Y : PairType) (s : ℕ) : shiftKernel X Y s ≠ ⊤ :=
    ENNReal.ne_top_of_tsum_ne_top (shiftKernel_row_ne_top hbound X Y) s
  have hcoef (Y : PairType) (s n : ℕ) :
      0 ≤ (kernelLengthCoefficient X Y s n : ℝ) := by
    exact_mod_cast kernelLengthCoefficient_nonneg X Y s n
  have htotal : (∑' j : PairType × ℕ, shiftKernel X j.1 j.2) ≠ ⊤ := by
    rw [ENNReal.tsum_prod', tsum_fintype]
    exact ENNReal.sum_ne_top.mpr (fun Y _ => shiftKernel_row_ne_top hbound X Y)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro Y s
    have hs := ENNReal.summable_toReal (hshift Y s)
    exact hs.congr (fun n => ENNReal.toReal_ofReal (hcoef Y s n))
  · intro Y s
    unfold realKernel shiftKernel
    rw [ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
    exact tsum_congr (fun n => ENNReal.toReal_ofReal (hcoef Y s n))
  · intro Y s
    exact ENNReal.toReal_nonneg
  · exact (ENNReal.summable_toReal htotal).mul_right 2

/-- Every finite length cutoff is dominated by the full real renewal action. -/
theorem main : AKLT.Blueprint.Rec.FiniteKernelTailDominationStatement :=
  main_of_residual kernelSeriesBridge

end AKLT.W.REC072
