import AKLT.W.REC070.Budget
import AKLT.W.REC070.Mass
import AKLT.W.REC070.Shift

noncomputable section
open scoped BigOperators ENNReal
open AKLT.Defs AKLT.Blueprint.Rec
namespace AKLT.W.REC070
set_option maxHeartbeats 2000000

/-- A finite real sum; the infinite rows continue to live in ENNReal. -/
def rowReal (θ : ℝ) (X : PairType) (n : ℕ) : ℝ :=
  ∑ Y : PairType, ∑ s ∈ Finset.range (n + 2),
    (kernelLengthCoefficient X Y s n : ℝ) * witnessReal Y * θ^(-(s : ℤ))

lemma coefficient_real_nonneg (X Y : PairType) (s n : ℕ) :
    0 ≤ (kernelLengthCoefficient X Y s n : ℝ) :=
  Rat.cast_nonneg.mpr (coefficient_nonneg X Y s n)

lemma rowReal_nonneg (θ : ℝ) (hθ : 0 < θ) (X : PairType) (n : ℕ) : 0 ≤ rowReal θ X n := by
  apply Finset.sum_nonneg
  intro Y _
  apply Finset.sum_nonneg
  intro s _
  exact mul_nonneg (mul_nonneg (coefficient_real_nonneg X Y s n) (witness_positive Y).le) (zpow_pos hθ _).le

lemma rowLength_real (θ : ℝ) (hθ : 0 < θ) (X : PairType) (n : ℕ) :
    RowLength θ X n = ENNReal.ofReal (rowReal θ X n) := by
  have hterm (Y : PairType) (s : ℕ) :
      0 ≤ (kernelLengthCoefficient X Y s n : ℝ) * witnessReal Y * θ^(-(s : ℤ)) :=
    mul_nonneg (mul_nonneg (coefficient_real_nonneg X Y s n) (witness_positive Y).le) (zpow_pos hθ _).le
  unfold RowLength rowReal
  rw [ENNReal.ofReal_sum_of_nonneg (by intro Y _; exact Finset.sum_nonneg (fun s _ => hterm Y s))]
  apply Finset.sum_congr rfl
  intro Y _
  rw [ENNReal.ofReal_sum_of_nonneg (by intro s _; exact hterm Y s)]
  apply Finset.sum_congr rfl
  intro s _
  rw [ENNReal.ofReal_mul (mul_nonneg (coefficient_real_nonneg X Y s n) (witness_positive Y).le),
    ENNReal.ofReal_mul (coefficient_real_nonneg X Y s n)]

lemma budget_factor (b q : ℝ) (hb : 0 < b) (n : ℕ) :
    q^n * b^(-(n : ℤ) - 2) = b^(-2 : ℤ) * (q / b)^n := by
  rw [show -(n : ℤ) - 2 = (-2 : ℤ) + -(n : ℤ) by omega, zpow_add₀ hb.ne']
  simp only [zpow_neg, zpow_natCast, div_eq_mul_inv]
  ring

lemma lengthIncrement_proved : Residual_LengthIncrement := by
  intro CV q hOpen θ hθ hθ1 X n
  let b : ℝ := (1 + q) / 2
  let E : ℝ := (1 - θ) * (n + 1 : ℝ) * b^(-(n : ℤ) - 2)
  let M : ℝ := ∑ Y : PairType, ∑ s ∈ Finset.range (n + 2),
    (kernelLengthCoefficient X Y s n : ℝ) * witnessReal Y
  have hb : 0 < b := by dsimp [b]; linarith [hOpen.2.1]
  have hθ0 : 0 < θ := hb.trans hθ
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hM : 0 ≤ M := by
    apply Finset.sum_nonneg
    intro Y _
    apply Finset.sum_nonneg
    intro s _
    exact mul_nonneg (coefficient_real_nonneg X Y s n) (witness_positive Y).le
  have hMbound : M ≤ witnessRatio * witnessReal X * ((n : ℝ) * (responseCap : ℝ) * CV * q^n) :=
    weighted_mass_bound CV q hOpen X n
  have hfinite : rowReal θ X n ≤ M +
      witnessRatio * witnessReal X * ((n : ℝ) * (responseCap : ℝ) * CV * q^n) * E := by
    calc
      _ ≤ ∑ Y : PairType, ∑ s ∈ Finset.range (n + 2),
          ((kernelLengthCoefficient X Y s n : ℝ) * witnessReal Y +
            (kernelLengthCoefficient X Y s n : ℝ) * witnessReal Y * E) := by
        apply Finset.sum_le_sum
        intro Y _
        apply Finset.sum_le_sum
        intro s hs
        have hsn : s ≤ n + 1 := by simp only [Finset.mem_range] at hs; omega
        have hi := (shift_increment b θ hb hθ hθ1 n s hsn).2
        have hc := mul_nonneg (coefficient_real_nonneg X Y s n) (witness_positive Y).le
        have := mul_le_mul_of_nonneg_left hi hc
        dsimp [E] at *
        nlinarith
      _ = M + M * E := by simp only [Finset.sum_add_distrib, ← Finset.sum_mul, M]
      _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_right hMbound hE)
  have hidentity : witnessRatio * witnessReal X * ((n : ℝ) * (responseCap : ℝ) * CV * q^n) * E =
      (1 - θ) * witnessRatio *
        (18094 / 100000 + 2 * (36751 / 100000 : ℝ)) * CV * b^(-2 : ℤ) *
        (n : ℝ) * (n + 1 : ℝ) * (q / b)^n * witnessReal X := by
    have hh := budget_factor b q hb n
    dsimp [E]
    push_cast [responseCap]
    calc
      _ = (1 - θ) * witnessRatio * witnessReal X * (n : ℝ) *
          (18094 / 100000 + 2 * (36751 / 100000 : ℝ)) * CV * (n + 1 : ℝ) *
          (q^n * b^(-(n : ℤ) - 2)) := by ring
      _ = _ := by rw [hh]; ring
  have hMrow : rowReal 1 X n = M := by simp [rowReal, M]
  rw [rowLength_real θ hθ0, rowLength_real 1 (by norm_num), hMrow]
  unfold RowLengthError
  change ENNReal.ofReal (rowReal θ X n) ≤ ENNReal.ofReal M +
    ENNReal.ofReal ((1 - θ) * witnessRatio *
      (18094 / 100000 + 2 * (36751 / 100000 : ℝ)) * CV * b^(-2 : ℤ) *
      (n : ℝ) * (n + 1 : ℝ) * (q / b)^n * witnessReal X)
  rw [← hidentity, ← ENNReal.ofReal_add hM (by
    exact mul_nonneg (mul_nonneg (mul_nonneg
      (by norm_num [witnessRatio, witnessReal, kernelWitness]) (witness_positive X).le)
      (by have := hOpen.1; have := hOpen.2.1; norm_num [responseCap]; positivity)) hE)]
  exact ENNReal.ofReal_le_ofReal hfinite

end AKLT.W.REC070
