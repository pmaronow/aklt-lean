module
public import AKLT.Blueprint.Rec.NodesKernel

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators ENNReal
open AKLT.Blueprint.Rec

namespace AKLT.W.REC066

private theorem majorant_summable (CV q θ : ℝ)
    (hq : 0 < q) (hθ : q ^ 2 < θ) :
    Summable (fun n : ℕ => kernelMajorant CV q θ n) := by
  have hθpos : 0 < θ := lt_of_lt_of_le (sq_pos_of_pos hq) (le_of_lt hθ)
  have hsqrt : 0 < Real.sqrt θ := Real.sqrt_pos.2 hθpos
  have hqsqrt : q < Real.sqrt θ := (Real.lt_sqrt hq.le).2 hθ
  let r : ℝ := q * Real.rpow θ (-(1 / 2 : ℝ))
  have hr_eq : r = q / Real.sqrt θ := by
    dsimp [r]
    rw [Real.rpow_neg hθpos.le, ← Real.sqrt_eq_rpow θ]
    rw [div_eq_mul_inv]
  have hr_nonneg : 0 ≤ r := by
    rw [hr_eq]
    positivity
  have hr_lt : r < 1 := by
    rw [hr_eq]
    exact (div_lt_one hsqrt).2 hqsqrt
  have hpow : ∀ n : ℕ, Real.rpow θ (-(n : ℝ) / 2) =
      (Real.rpow θ (-(1 / 2 : ℝ))) ^ n := by
    intro n
    calc
      Real.rpow θ (-(n : ℝ) / 2) =
          Real.rpow θ ((-(1 / 2 : ℝ)) * (n : ℝ)) := by ring_nf
      _ = Real.rpow (Real.rpow θ (-(1 / 2 : ℝ))) (n : ℝ) :=
        Real.rpow_mul hθpos.le _ _
      _ = (Real.rpow θ (-(1 / 2 : ℝ))) ^ n := Real.rpow_natCast _ _
  have hterm : ∀ n : ℕ,
      kernelMajorant CV q θ n =
        ((18094 / 100000 + 2 * (36751 / 100000 : ℝ)) * CV * θ⁻¹) *
          (n : ℝ) * r ^ n := by
    intro n
    rw [kernelMajorant]
    rw [show (-(n : ℝ) / 2 - 1) = (-(n : ℝ) / 2) + (-1 : ℝ) by ring]
    calc
      (n : ℝ) * (18094 / 100000 + 2 * (36751 / 100000 : ℝ)) * CV * q ^ n *
          Real.rpow θ (-(n : ℝ) / 2 + (-1 : ℝ)) =
        ((n : ℝ) * (18094 / 100000 + 2 * (36751 / 100000 : ℝ)) * CV * q ^ n) *
          Real.rpow θ (-(n : ℝ) / 2 + (-1 : ℝ)) := by ring
      _ = ((n : ℝ) * (18094 / 100000 + 2 * (36751 / 100000 : ℝ)) * CV * q ^ n) *
          (Real.rpow θ (-(n : ℝ) / 2) * Real.rpow θ (-1 : ℝ)) :=
        congrArg (fun z : ℝ =>
          ((n : ℝ) * (18094 / 100000 + 2 * (36751 / 100000 : ℝ)) * CV * q ^ n) * z)
          (Real.rpow_add hθpos _ _)
      _ = ((18094 / 100000 + 2 * (36751 / 100000 : ℝ)) * CV * θ⁻¹) *
          (n : ℝ) * r ^ n := by
        rw [hpow n]
        calc
          (n : ℝ) * (18094 / 100000 + 2 * (36751 / 100000 : ℝ)) * CV * q ^ n *
              (Real.rpow θ (-(1 / 2 : ℝ)) ^ n * Real.rpow θ (-1 : ℝ)) =
            ((n : ℝ) * (18094 / 100000 + 2 * (36751 / 100000 : ℝ)) * CV * q ^ n) *
              (Real.rpow θ (-(1 / 2 : ℝ)) ^ n * θ⁻¹) := by
                congr 1
                exact congrArg (fun z : ℝ => Real.rpow θ (-(1 / 2 : ℝ)) ^ n * z)
                  (Real.rpow_neg_one θ)
          _ = ((18094 / 100000 + 2 * (36751 / 100000 : ℝ)) * CV * θ⁻¹) *
                (n : ℝ) * r ^ n := by
              have hprod : q ^ n *
                  (Real.rpow θ (-(1 / 2 : ℝ)) ^ n * θ⁻¹) =
                  (q * Real.rpow θ (-(1 / 2 : ℝ))) ^ n * θ⁻¹ := by
                calc
                  q ^ n * (Real.rpow θ (-(1 / 2 : ℝ)) ^ n * θ⁻¹) =
                      (q ^ n * Real.rpow θ (-(1 / 2 : ℝ)) ^ n) * θ⁻¹ := by ring
                  _ = (q * Real.rpow θ (-(1 / 2 : ℝ))) ^ n * θ⁻¹ := by
                    rw [← mul_pow]
              calc
                (n : ℝ) * (18094 / 100000 + 2 * (36751 / 100000 : ℝ)) * CV *
                    q ^ n * (Real.rpow θ (-(1 / 2 : ℝ)) ^ n * θ⁻¹) =
                  ((n : ℝ) * (18094 / 100000 + 2 * (36751 / 100000 : ℝ)) * CV) *
                    (q ^ n * (Real.rpow θ (-(1 / 2 : ℝ)) ^ n * θ⁻¹)) := by ring
                _ = ((n : ℝ) * (18094 / 100000 + 2 * (36751 / 100000 : ℝ)) * CV) *
                    ((q * Real.rpow θ (-(1 / 2 : ℝ))) ^ n * θ⁻¹) :=
                      congrArg _ hprod
                _ = ((18094 / 100000 + 2 * (36751 / 100000 : ℝ)) * CV * θ⁻¹) *
                    (n : ℝ) * r ^ n := by
                  dsimp [r]
                  ring
  have hrnorm : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr_nonneg]
    exact hr_lt
  have hbase : Summable (fun n : ℕ => (n : ℝ) * r ^ n) := by
    simpa [pow_one] using
      (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hrnorm)
  have hscaled : Summable (fun n : ℕ =>
      ((18094 / 100000 + 2 * (36751 / 100000 : ℝ)) * CV * θ⁻¹) *
        ((n : ℝ) * r ^ n)) := hbase.mul_left _
  exact hscaled.congr fun n => by rw [hterm n]; ring

theorem main : AKLT.Blueprint.Rec.MajorantFiniteStatement := by
  intro CV q hOpen θ hqθ hθ1
  rcases hOpen with ⟨hCV, hq, hq1, _⟩
  have hθpos : 0 < θ := lt_of_lt_of_le (sq_pos_of_pos hq) (le_of_lt hqθ)
  have hnonneg : ∀ n : ℕ, 0 ≤ kernelMajorant CV q θ n := by
    intro n
    rw [kernelMajorant]
    positivity [Real.rpow_pos_of_pos hθpos (-(n : ℝ) / 2 - 1)]
  have hs : Summable (fun n : ℕ => kernelMajorant CV q θ n) :=
    majorant_summable CV q θ hq hqθ
  rw [← ENNReal.ofReal_tsum_of_nonneg hnonneg hs]
  exact ENNReal.ofReal_ne_top

end AKLT.W.REC066

#print axioms AKLT.W.REC066.main
