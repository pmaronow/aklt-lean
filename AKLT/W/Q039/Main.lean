import AKLT.Blueprint.Q.NodesQuantum

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Q

namespace AKLT.W.Q039

theorem main : AKLT.Blueprint.Q.DeterminantModulusStatement := by
  intro a b z w hz hw
  have h00a : Complex.normSq (z 0) = (1 + a 2) / 2 := by
    have h := congrFun (congrFun hz.2 0) 0
    have h' : (Complex.normSq (z 0) : ℂ) = (2 : ℂ)⁻¹ * (1 + (a 2 : ℂ)) := by
      simpa [spinDensity, pauli, Fin.sum_univ_succ, Complex.star_def,
        Complex.mul_conj] using h
    have h'' : (Complex.normSq (z 0) : ℂ) = (((1 + a 2) / 2 : ℝ) : ℂ) := by
      calc
        _ = (2 : ℂ)⁻¹ * (1 + (a 2 : ℂ)) := h'
        _ = _ := by push_cast; ring
    exact_mod_cast h''
  have h11a : Complex.normSq (z 1) = (1 - a 2) / 2 := by
    have h := congrFun (congrFun hz.2 1) 1
    have h' : (Complex.normSq (z 1) : ℂ) = (2 : ℂ)⁻¹ * (1 - (a 2 : ℂ)) := by
      convert (by simpa [spinDensity, pauli, Fin.sum_univ_succ,
        Complex.star_def, Complex.mul_conj] using h) using 1 <;> ring
    have h'' : (Complex.normSq (z 1) : ℂ) = (((1 - a 2) / 2 : ℝ) : ℂ) := by
      calc
        _ = (2 : ℂ)⁻¹ * (1 - (a 2 : ℂ)) := h'
        _ = _ := by push_cast; ring
    exact_mod_cast h''
  have h01a : z 0 * star (z 1) = ((a 0 : ℝ) - Complex.I * (a 1 : ℝ)) / 2 := by
    have h := congrFun (congrFun hz.2 0) 1
    have h' : z 0 * star (z 1) = (2 : ℂ)⁻¹ * ((a 0 : ℂ) - (a 1 : ℂ) * Complex.I) := by
      convert (by simpa [spinDensity, pauli, Fin.sum_univ_succ,
        Complex.star_def] using h) using 1 <;> simp only [starRingEnd_apply] <;> ring
    convert h' using 1 <;> push_cast <;> ring
  have h10b : w 1 * star (w 0) = ((b 0 : ℝ) + Complex.I * (b 1 : ℝ)) / 2 := by
    have h := congrFun (congrFun hw.2 1) 0
    have h' : w 1 * star (w 0) = (2 : ℂ)⁻¹ * ((b 0 : ℂ) + (b 1 : ℂ) * Complex.I) := by
      simpa [spinDensity, pauli, Fin.sum_univ_succ, Complex.star_def] using h
    convert h' using 1 <;> push_cast <;> ring
  have h11b : Complex.normSq (w 1) = (1 - b 2) / 2 := by
    have h := congrFun (congrFun hw.2 1) 1
    have h' : (Complex.normSq (w 1) : ℂ) = (2 : ℂ)⁻¹ * (1 - (b 2 : ℂ)) := by
      convert (by simpa [spinDensity, pauli, Fin.sum_univ_succ,
        Complex.star_def, Complex.mul_conj] using h) using 1 <;> ring
    have h'' : (Complex.normSq (w 1) : ℂ) = (((1 - b 2) / 2 : ℝ) : ℂ) := by
      calc
        _ = (2 : ℂ)⁻¹ * (1 - (b 2 : ℂ)) := h'
        _ = _ := by push_cast; ring
    exact_mod_cast h''
  have h00b : Complex.normSq (w 0) = (1 + b 2) / 2 := by
    have h := congrFun (congrFun hw.2 0) 0
    have h' : (Complex.normSq (w 0) : ℂ) = (2 : ℂ)⁻¹ * (1 + (b 2 : ℂ)) := by
      simpa [spinDensity, pauli, Fin.sum_univ_succ, Complex.star_def,
        Complex.mul_conj] using h
    have h'' : (Complex.normSq (w 0) : ℂ) = (((1 + b 2) / 2 : ℝ) : ℂ) := by
      calc
        _ = (2 : ℂ)⁻¹ * (1 + (b 2 : ℂ)) := h'
        _ = _ := by push_cast; ring
    exact_mod_cast h''
  have hcross : ((z 0 * w 1) * star (z 1 * w 0)).re =
      (a 0 * b 0 + a 1 * b 1) / 4 := by
    calc
      ((z 0 * w 1) * star (z 1 * w 0)).re =
          ((z 0 * star (z 1)) * (w 1 * star (w 0))).re := by
            rw [star_mul]
            congr 1 <;> ring
      _ = ((((a 0 : ℝ) - Complex.I * (a 1 : ℝ)) / 2) *
            (((b 0 : ℝ) + Complex.I * (b 1 : ℝ)) / 2)).re := by rw [h01a, h10b]
      _ = (a 0 * b 0 + a 1 * b 1) / 4 := by
            simp [Complex.mul_re]
            ring
  rw [determinant, Complex.normSq_sub, Complex.normSq_mul, Complex.normSq_mul]
  rw [← Complex.star_def, h00a, h11b, h11a, h00b, hcross]
  simp only [dot, Fin.sum_univ_succ]
  norm_num [Fin.succ]
  ring

end AKLT.W.Q039
