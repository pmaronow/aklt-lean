import AKLT.Blueprint.Mom.NodesMean

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.MOM030

private def householder (u : Vec3) (n : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => (if i = j then 1 else 0) - 2 * u i * u j / n

private theorem householder_mulVec (u v : Vec3) (n : ℝ) :
    (householder u n).mulVec v = fun i => v i - (2 * dot u v / n) * u i := by
  ext i
  fin_cases i <;>
    simp [householder, Matrix.mulVec, dotProduct, dot, Fin.sum_univ_three] <;> ring

private theorem householder_orthogonal (u : Vec3) (n : ℝ) (hn : normSq u = n)
    (hne : n ≠ 0) :
    (householder u n).transpose * householder u n = 1 := by
  have hn' : u 0 * u 0 + u 1 * u 1 + u 2 * u 2 = n := by
    simpa [normSq, dot, Fin.sum_univ_three] using hn
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [householder, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three] <;>
    field_simp [hne] <;>
    rw [← hn'] <;>
    ring

theorem main : AKLT.Blueprint.Mom.OrthogonalTransportStatement := by
  intro v w hvw
  by_cases heq : v = w
  · subst w
    exact ⟨1, by simp, by simp⟩
  · let u : Vec3 := fun i => v i - w i
    have hu : u ≠ 0 := by
      intro hzero
      apply heq
      funext i
      have hi := congrFun hzero i
      dsimp [u] at hi
      linarith
    have hdot : 2 * dot u v = normSq u := by
      dsimp [u, normSq, dot] at *
      simp only [Fin.sum_univ_three] at hvw ⊢
      nlinarith
    have hnpos : 0 < normSq u := by
      by_contra hnot
      have hnnonneg : 0 ≤ normSq u := by
        change 0 ≤ ∑ i, u i * u i
        exact Finset.sum_nonneg fun i _ => mul_self_nonneg (u i)
      have hnzero : normSq u = 0 := by linarith
      have hcoords : ∀ i, u i = 0 := by
        intro i
        have hsum : (u 0) * (u 0) + (u 1) * (u 1) + (u 2) * (u 2) = 0 := by
          simpa [normSq, dot, Fin.sum_univ_three] using hnzero
        fin_cases i
        · have hz : u 0 * u 0 = 0 := by
            nlinarith [mul_self_nonneg (u 1), mul_self_nonneg (u 2)]
          exact (mul_self_eq_zero.mp hz)
        · have hz : u 1 * u 1 = 0 := by
            nlinarith [mul_self_nonneg (u 0), mul_self_nonneg (u 2)]
          exact (mul_self_eq_zero.mp hz)
        · have hz : u 2 * u 2 = 0 := by
            nlinarith [mul_self_nonneg (u 0), mul_self_nonneg (u 1)]
          exact (mul_self_eq_zero.mp hz)
      apply hu
      funext i
      exact hcoords i
    let R := householder u (normSq u)
    refine ⟨R, ?_, ?_⟩
    · exact householder_orthogonal u (normSq u) rfl
        (ne_of_gt hnpos)
    · rw [householder_mulVec]
      ext i
      dsimp [u]
      rw [hdot]
      rw [div_self (ne_of_gt hnpos)]
      ring

end AKLT.W.MOM030

#print axioms AKLT.W.MOM030.main
