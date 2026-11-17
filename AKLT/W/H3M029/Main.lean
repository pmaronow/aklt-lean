module
public import AKLT.Blueprint.H3.NodesKernel

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators ENNReal
open AKLT.Defs
open AKLT.Blueprint.H3

namespace AKLT.W.H3M029

private def kernelTerm (X Y : PairType) (s n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (kernelLengthCoefficient X Y s n : ℝ) *
    ENNReal.ofReal (kernelWitness Y : ℝ)

private theorem reorderKernelTerms (X : PairType) :
    (∑ Y : PairType, ∑' s : ℕ, ∑' n : ℕ, kernelTerm X Y s n) =
      ∑' n : ℕ, ∑' s : ℕ, ∑ Y : PairType, kernelTerm X Y s n := by
  have hY : (∑ Y : PairType, ∑' s : ℕ, ∑' n : ℕ, kernelTerm X Y s n) =
      ∑' Y : PairType, ∑' s : ℕ, ∑' n : ℕ, kernelTerm X Y s n := by
    symm
    exact tsum_fintype _
  have hInner : (fun s : ℕ => ∑' Y : PairType, ∑' n : ℕ, kernelTerm X Y s n) =
      fun s => ∑' n : ℕ, ∑' Y : PairType, kernelTerm X Y s n := by
    funext s
    exact ENNReal.tsum_comm
  calc
    (∑ Y : PairType, ∑' s : ℕ, ∑' n : ℕ, kernelTerm X Y s n) =
        ∑' Y : PairType, ∑' s : ℕ, ∑' n : ℕ, kernelTerm X Y s n := hY
    _ = ∑' s : ℕ, ∑' Y : PairType, ∑' n : ℕ, kernelTerm X Y s n :=
      ENNReal.tsum_comm
    _ = ∑' s : ℕ, ∑' n : ℕ, ∑' Y : PairType, kernelTerm X Y s n := by
      rw [hInner]
    _ = ∑' n : ℕ, ∑' s : ℕ, ∑' Y : PairType, kernelTerm X Y s n :=
      ENNReal.tsum_comm
    _ = ∑' n : ℕ, ∑' s : ℕ, ∑ Y : PairType, kernelTerm X Y s n := by
      simp only [tsum_fintype]

theorem main : AKLT.Blueprint.H3.KernelSeriesRegroupingStatement := by
  classical
  intro X hzero hrow
  have hregroup :
      (∑ Y : PairType, shiftedKernel 1 X Y * ENNReal.ofReal (kernelWitness Y : ℝ)) =
        ∑' n : ℕ, ∑' s : ℕ, ∑ Y : PairType, kernelTerm X Y s n := by
    calc
      (∑ Y : PairType, shiftedKernel 1 X Y * ENNReal.ofReal (kernelWitness Y : ℝ)) =
          ∑ Y : PairType, ∑' s : ℕ, ∑' n : ℕ, kernelTerm X Y s n := by
        apply Finset.sum_congr rfl
        intro Y hY
        simp only [shiftedKernel, one_zpow, ENNReal.ofReal_one, mul_one]
        rw [ENNReal.tsum_mul_right.symm]
        simp only [shiftKernel]
        congr 1
        funext s
        exact ENNReal.tsum_mul_right.symm
      _ = ∑' n : ℕ, ∑' s : ℕ, ∑ Y : PairType, kernelTerm X Y s n :=
        reorderKernelTerms X
  have hfinite (n : ℕ) :
      (∑' s : ℕ, ∑ Y : PairType, kernelTerm X Y s n) =
        ENNReal.ofReal (kernelLengthRow X n : ℝ) := by
    calc
      (∑' s : ℕ, ∑ Y : PairType, kernelTerm X Y s n) =
          ∑ s ∈ lengthShifts X n, ∑ Y : PairType, kernelTerm X Y s n := by
        apply tsum_eq_sum
        intro s hs
        apply Finset.sum_eq_zero
        intro Y hY
        simp [kernelTerm, hzero Y n s hs]
      _ = ∑ Y : PairType, ∑ s ∈ lengthShifts X n, kernelTerm X Y s n := by
        rw [Finset.sum_comm]
      _ = ENNReal.ofReal (kernelLengthRow X n : ℝ) := by
        have hmul (Y : PairType) (s : ℕ) :
            kernelTerm X Y s n =
              ENNReal.ofReal ((kernelLengthCoefficient X Y s n : ℚ) * kernelWitness Y : ℝ) := by
          dsimp [kernelTerm]
          have hcoeff : (0 : ℝ) ≤ (kernelLengthCoefficient X Y s n : ℝ) := by
            exact_mod_cast kernelLengthCoefficient_nonneg X Y s n
          rw [← ENNReal.ofReal_mul hcoeff]
        simp_rw [hmul]
        have hInnerSum (Y : PairType) :
            (∑ s ∈ lengthShifts X n,
                ENNReal.ofReal ((kernelLengthCoefficient X Y s n : ℚ) * kernelWitness Y : ℝ)) =
              ENNReal.ofReal (∑ s ∈ lengthShifts X n,
                ((kernelLengthCoefficient X Y s n : ℚ) * kernelWitness Y : ℚ) : ℝ) := by
          rw [← ENNReal.ofReal_sum_of_nonneg]
          · congr 1
            norm_cast
          · intro s hs
            exact_mod_cast mul_nonneg (kernelLengthCoefficient_nonneg X Y s n)
              (kernelWitness_pos Y).le
        have hOuterSum :
            (∑ Y : PairType,
                ENNReal.ofReal (∑ s ∈ lengthShifts X n,
                  ((kernelLengthCoefficient X Y s n : ℚ) * kernelWitness Y : ℚ) : ℝ)) =
              ENNReal.ofReal (∑ Y : PairType, ∑ s ∈ lengthShifts X n,
                kernelLengthCoefficient X Y s n * kernelWitness Y : ℚ) := by
          rw [← ENNReal.ofReal_sum_of_nonneg]
          · congr 1
            norm_cast
          · intro Y hY
            exact_mod_cast Finset.sum_nonneg fun s hs =>
              mul_nonneg (kernelLengthCoefficient_nonneg X Y s n) (kernelWitness_pos Y).le
        calc
          (∑ Y : PairType, ∑ s ∈ lengthShifts X n,
              ENNReal.ofReal ((kernelLengthCoefficient X Y s n : ℚ) * kernelWitness Y : ℝ)) =
              ∑ Y : PairType, ENNReal.ofReal (∑ s ∈ lengthShifts X n,
                ((kernelLengthCoefficient X Y s n : ℚ) * kernelWitness Y : ℚ) : ℝ) := by
                  apply Finset.sum_congr rfl
                  intro Y hY
                  exact hInnerSum Y
          _ = ENNReal.ofReal (∑ Y : PairType, ∑ s ∈ lengthShifts X n,
                kernelLengthCoefficient X Y s n * kernelWitness Y : ℚ) := hOuterSum
          _ = ENNReal.ofReal (kernelLengthRow X n : ℝ) := by
                rw [← hrow n]
  calc
    (∑ Y : PairType, shiftedKernel 1 X Y * ENNReal.ofReal (kernelWitness Y : ℝ)) =
        ∑' n : ℕ, ∑' s : ℕ, ∑ Y : PairType, kernelTerm X Y s n := hregroup
    _ = ∑' n : ℕ, ENNReal.ofReal (kernelLengthRow X n : ℝ) := by
      congr 1
      funext n
      exact hfinite n

end AKLT.W.H3M029

namespace AKLT.W.H3M029
#print axioms main
end AKLT.W.H3M029
