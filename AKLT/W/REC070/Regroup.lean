module
public import AKLT.W.REC070.Budget
public import AKLT.W.REC070.Foundations

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators ENNReal
open AKLT.Defs AKLT.Blueprint.Rec

namespace AKLT.W.REC070
set_option maxHeartbeats 1000000

lemma rowExpansion_proved : Residual_RowExpansion := by
  intro θ _ X
  calc
    (∑ Y : PairType, shiftedKernel θ X Y * ENNReal.ofReal (witnessReal Y)) =
        ∑' Y : PairType, ∑' s : ℕ, ∑' n : ℕ,
          ENNReal.ofReal (kernelLengthCoefficient X Y s n : ℝ) *
            ENNReal.ofReal (witnessReal Y) * ENNReal.ofReal (θ ^ (-(s : ℤ))) := by
      simp only [tsum_fintype, shiftedKernel, shiftKernel, ← ENNReal.tsum_mul_right]
      apply Finset.sum_congr rfl
      intro Y _
      apply tsum_congr
      intro s
      apply tsum_congr
      intro n
      ac_rfl
    _ = ∑' n : ℕ, ∑' Y : PairType, ∑' s : ℕ,
          ENNReal.ofReal (kernelLengthCoefficient X Y s n : ℝ) *
            ENNReal.ofReal (witnessReal Y) * ENNReal.ofReal (θ ^ (-(s : ℤ))) := by
      calc
        _ = ∑' Y : PairType, ∑' n : ℕ, ∑' s : ℕ,
            ENNReal.ofReal (kernelLengthCoefficient X Y s n : ℝ) *
              ENNReal.ofReal (witnessReal Y) * ENNReal.ofReal (θ ^ (-(s : ℤ))) := by
          apply tsum_congr
          intro Y
          exact ENNReal.tsum_comm
        _ = _ := ENNReal.tsum_comm
    _ = ∑' n : ℕ, RowLength θ X n := by
      apply tsum_congr
      intro n
      simp only [tsum_fintype, RowLength]
      apply Finset.sum_congr rfl
      intro Y _
      apply tsum_eq_sum
      intro s hs
      have h : n + 1 < s := by simp only [Finset.mem_range] at hs; omega
      simp [coefficient_support X Y n s h]

end AKLT.W.REC070
