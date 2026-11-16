import AKLT.Blueprint.Q.NodesTight

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Q

namespace AKLT.W.Q010

private theorem scaleQuartic (a b c : ℂ) (r s q : ℕ)
    (hs : r + s + q = 4) :
    (a / 2) ^ r * (b / 2) ^ s * (c / 2) ^ q =
      (1 / 16 : ℂ) * a ^ r * b ^ s * c ^ q := by
  simp only [div_eq_mul_inv]
  have hscale : (2 : ℂ)⁻¹ ^ r * (2 : ℂ)⁻¹ ^ s * (2 : ℂ)⁻¹ ^ q = (1 / 16 : ℂ) := by
    rw [← pow_add, ← pow_add, hs]
    norm_num
  calc
    _ = ((2 : ℂ)⁻¹ ^ r * (2 : ℂ)⁻¹ ^ s * (2 : ℂ)⁻¹ ^ q) *
          (a ^ r * b ^ s * c ^ q) := by ring
    _ = _ := by
      rw [hscale]
      rw [show (1 / 16 : ℂ) = 1 * (16 : ℂ)⁻¹ by norm_num]
      ring

theorem main : AKLT.Blueprint.Q.QuarticKernelEvaluationStatement := by
  intro v z hz j k
  let x : ℂ := (v 0 : ℂ)
  let y : ℂ := (v 1 : ℂ)
  let t : ℂ := (v 2 : ℂ)
  have h00 := congrFun (congrFun hz.2 0) 0
  have h11 := congrFun (congrFun hz.2 1) 1
  have h10 := congrFun (congrFun hz.2 1) 0
  have hp00 : z 0 * star (z 0) = (1 + t) / 2 := by
    have hh : z 0 * star (z 0) = 2⁻¹ * (1 + t) := by
      simpa [x, y, t, spinDensity, pauli, Fin.sum_univ_three] using h00
    rw [hh]
    ring
  have hp11 : z 1 * star (z 1) = (1 - t) / 2 := by
    have hh : z 1 * star (z 1) = 2⁻¹ * (1 + -t) := by
      simpa [x, y, t, spinDensity, pauli, Fin.sum_univ_three] using h11
    rw [hh]
    ring
  have hp10 : z 1 * star (z 0) = (x + Complex.I * y) / 2 := by
    have hh : z 1 * star (z 0) = 2⁻¹ * (x + y * Complex.I) := by
      simpa [x, y, t, spinDensity, pauli, Fin.sum_univ_three] using h10
    rw [hh]
    ring
  have hp01 : z 0 * star (z 1) = (x - Complex.I * y) / 2 := by
    have h01 := congrFun (congrFun hz.2 0) 1
    have hh : z 0 * star (z 1) = 2⁻¹ * (x + -(y * Complex.I)) := by
      simpa [x, y, t, spinDensity, pauli, Fin.sum_univ_three] using h01
    rw [hh]
    ring
  by_cases hjk : j ≤ k
  · have hj : j.val ≤ k.val := hjk
    let m := 4 - k.val
    let d := k.val - j.val
    have hm : 4 - j.val = m + d := by dsimp [m, d]; omega
    have hk : k.val = j.val + d := by dsimp [d]; omega
    have hmk : 4 - (j.val + d) = m := by dsimp [m]; omega
    have hpair :
        star (z 0 ^ (4 - j.val) * z 1 ^ j.val) *
            (z 0 ^ (4 - k.val) * z 1 ^ k.val) =
          (z 0 * star (z 0)) ^ (4 - k.val) *
            (z 1 * star (z 1)) ^ j.val *
            (z 1 * star (z 0)) ^ (k.val - j.val) := by
      calc
        _ = star (z 0) ^ (4 - j.val) * star (z 1) ^ j.val *
              z 0 ^ (4 - k.val) * z 1 ^ k.val := by
                simp only [star_mul, star_pow]
                ring
        _ = star (z 0) ^ (m + d) * star (z 1) ^ j.val *
              z 0 ^ m * z 1 ^ (j.val + d) := by rw [hm, hk, hmk]
        _ = (z 0 ^ m * star (z 0) ^ m) *
              (z 1 ^ j.val * star (z 1) ^ j.val) *
              (z 1 ^ d * star (z 0) ^ d) := by
                rw [pow_add, pow_add]
                ring
        _ = (z 0 * star (z 0)) ^ m *
              (z 1 * star (z 1)) ^ j.val *
              (z 1 * star (z 0)) ^ d := by
                rw [← mul_pow (z 0) (star (z 0)) m,
                  ← mul_pow (z 1) (star (z 1)) j.val,
                  ← mul_pow (z 1) (star (z 0)) d]
    rw [quarticMonomial, quarticMonomial, hpair]
    simp only [quarticKernel, if_pos hjk]
    simp only [map_mul, map_add, map_sub, map_pow, MvPolynomial.eval_C, MvPolynomial.eval_X,
      map_one]
    rw [hp00, hp11, hp10]
    have hs : m + j.val + d = 4 := by dsimp [m, d]; omega
    simpa [x, y, t] using scaleQuartic (1 + t) (1 - t) (x + Complex.I * y)
      m j.val d hs
  · have hkl : k < j := lt_of_not_ge hjk
    have hj : k.val < j.val := hkl
    let m := 4 - j.val
    let d := j.val - k.val
    have hk : 4 - k.val = m + d := by dsimp [m, d]; omega
    have hj' : j.val = k.val + d := by dsimp [d]; omega
    have hmk : 4 - (k.val + d) = m := by dsimp [m]; omega
    have hpair :
        star (z 0 ^ (4 - j.val) * z 1 ^ j.val) *
            (z 0 ^ (4 - k.val) * z 1 ^ k.val) =
          (z 0 * star (z 0)) ^ (4 - j.val) *
            (z 1 * star (z 1)) ^ k.val *
            (z 0 * star (z 1)) ^ (j.val - k.val) := by
      calc
        _ = star (z 0) ^ (4 - j.val) * star (z 1) ^ j.val *
              z 0 ^ (4 - k.val) * z 1 ^ k.val := by
                simp only [star_mul, star_pow]
                ring
        _ = star (z 0) ^ m * star (z 1) ^ (k.val + d) *
              z 0 ^ (m + d) * z 1 ^ k.val := by rw [hj', hk, hmk]
        _ = (z 0 ^ m * star (z 0) ^ m) *
              (z 1 ^ k.val * star (z 1) ^ k.val) *
              (z 0 ^ d * star (z 1) ^ d) := by
                rw [pow_add, pow_add]
                ring
        _ = (z 0 * star (z 0)) ^ m *
              (z 1 * star (z 1)) ^ k.val *
              (z 0 * star (z 1)) ^ d := by
                rw [← mul_pow (z 0) (star (z 0)) m,
                  ← mul_pow (z 1) (star (z 1)) k.val,
                  ← mul_pow (z 0) (star (z 1)) d]
    rw [quarticMonomial, quarticMonomial, hpair]
    simp only [quarticKernel, if_neg (by omega : ¬ j ≤ k)]
    simp only [map_mul, map_sub, map_pow, MvPolynomial.eval_C, MvPolynomial.eval_X, map_one]
    rw [hp00, hp11, hp01]
    have hs : m + k.val + d = 4 := by dsimp [m, d]; omega
    simpa [x, y, t] using scaleQuartic (1 + t) (1 - t) (x - Complex.I * y)
      m k.val d hs

end AKLT.W.Q010
