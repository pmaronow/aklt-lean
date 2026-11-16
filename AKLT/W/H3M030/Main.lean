import AKLT.Blueprint.H3.NodesKernel

open scoped BigOperators ENNReal
open AKLT.Blueprint.H3

namespace AKLT.W.H3M030

theorem main : AKLT.Blueprint.H3.CutoffSeriesLiftStatement := by
  intro f hf hzero B hcut
  have hB : 0 ≤ B := by
    have h := hcut 0
    simpa using h
  have hfinite (N : ℕ) : (∑ n ∈ Finset.range N, (f n : ℝ)) ≤ (B : ℝ) := by
    by_cases h0 : 0 ∈ Finset.range N
    · have hsub : (Finset.range N).erase 0 ⊆ Finset.Icc 1 N := by
        intro n hn
        simp only [Finset.mem_erase, Finset.mem_range] at hn
        simp only [Finset.mem_Icc]
        omega
      have hsumeq : (∑ n ∈ Finset.range N, (f n : ℝ)) =
          ∑ n ∈ (Finset.range N).erase 0, (f n : ℝ) := by
        have h := Finset.sum_erase_add (Finset.range N) (fun n => (f n : ℝ)) h0
        rw [show (f 0 : ℝ) = 0 by exact_mod_cast hzero] at h
        simpa using h.symm
      rw [hsumeq]
      have hcutR : (∑ n ∈ Finset.Icc 1 N, (f n : ℝ)) ≤ (B : ℝ) := by
        exact_mod_cast hcut N
      exact (Finset.sum_le_sum_of_subset_of_nonneg hsub (by
        intro n hn hnot
        exact_mod_cast hf n)).trans hcutR
    · have hN : N = 0 := by
        by_contra hn
        have : 0 ∈ Finset.range N := by simp [Finset.mem_range, Nat.pos_of_ne_zero hn]
        exact h0 this
      subst N
      simp [hB]
  rw [ENNReal.tsum_eq_iSup_nat]
  apply iSup_le
  intro N
  calc
    (∑ n ∈ Finset.range N, ENNReal.ofReal (f n : ℝ)) =
        ENNReal.ofReal (∑ n ∈ Finset.range N, (f n : ℝ)) := by
          symm
          apply ENNReal.ofReal_sum_of_nonneg
          intro n hn
          exact_mod_cast hf n
    _ ≤ ENNReal.ofReal (B : ℝ) := ENNReal.ofReal_le_ofReal (hfinite N)

end AKLT.W.H3M030

#print axioms AKLT.W.H3M030.main
