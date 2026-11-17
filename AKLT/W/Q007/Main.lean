import AKLT.Blueprint.Q.NodesFrames

noncomputable section

open AKLT.Defs

namespace AKLT.W.Q007

private theorem dot_cancel (A : Matrix (Fin 3) (Fin 3) ℝ)
    (x y : Vec3) (hA : A.transpose * A = 1) :
    dot (A.mulVec x) (A.mulVec y) = dot x y := by
  change (A.mulVec x) ⬝ᵥ (A.mulVec y) = x ⬝ᵥ y
  calc
    (A.mulVec x) ⬝ᵥ (A.mulVec y) =
        y ⬝ᵥ (A.transpose.mulVec (A.mulVec x)) := by
      exact (Matrix.dotProduct_transpose_mulVec A y (A.mulVec x)).symm
    _ = y ⬝ᵥ ((A.transpose * A).mulVec x) := by
      rw [Matrix.mulVec_mulVec]
    _ = y ⬝ᵥ x := by rw [hA]; simp
    _ = x ⬝ᵥ y := dotProduct_comm y x

theorem main : AKLT.Blueprint.Q.RelativeRotationStatement := by
  intro i j hij a b
  let T := frameRotation
  change ∃ k : ℕ, 1 ≤ k ∧ k ≤ 2 ∧ ∃ u v : IcoLetter,
      dot ((T ^ i.val).mulVec (icoVector a)) ((T ^ j.val).mulVec (icoVector b)) =
        dot (icoVector u) ((T ^ k).mulVec (icoVector v))
  have hT : T.transpose * T = 1 := by
    change frameRotation.transpose * frameRotation = 1
    ext p q
    fin_cases p <;> fin_cases q <;>
      norm_num [frameRotation, Matrix.mul_apply, Fin.sum_univ_succ]
  have hT2 : (T ^ 2).transpose * T ^ 2 = 1 := by
    rw [pow_two, Matrix.transpose_mul]
    calc
      _ = T.transpose * ((T.transpose * T) * T) := by
        simp only [mul_assoc]
      _ = 1 := by rw [hT, one_mul, hT]
  have hp : ∀ n : Fin 3, (T ^ n.val).transpose * (T ^ n.val) = 1 := by
    intro n
    fin_cases n
    · simp
    · simpa using hT
    · simpa using hT2
  have hcomm : ∀ n : Fin 3, ∀ x y : Vec3,
      dot ((T ^ n.val).mulVec x) ((T ^ n.val).mulVec y) = dot x y := by
    intro n x y
    exact dot_cancel (T ^ n.val) x y (hp n)
  fin_cases i <;> fin_cases j
  · exact (False.elim (hij rfl))
  · refine ⟨1, by norm_num, by norm_num, a, b, ?_⟩
    simp [pow_zero, pow_one]
  · refine ⟨2, by norm_num, by norm_num, a, b, ?_⟩
    simp [pow_zero]
  · refine ⟨1, by norm_num, by norm_num, b, a, ?_⟩
    simp only [pow_zero, Matrix.one_mulVec, pow_one]
    change (T.mulVec (icoVector a)) ⬝ᵥ icoVector b =
      icoVector b ⬝ᵥ (T.mulVec (icoVector a))
    exact dotProduct_comm _ _
  · exact (False.elim (hij rfl))
  · refine ⟨1, by norm_num, by norm_num, a, b, ?_⟩
    change dot ((T ^ 1).mulVec (icoVector a))
        ((T ^ 2).mulVec (icoVector b)) =
      dot (icoVector a) ((T ^ 1).mulVec (icoVector b))
    rw [pow_two, ← Matrix.mulVec_mulVec]
    have hc := hcomm (1 : Fin 3) (icoVector a) ((T ^ 1).mulVec (icoVector b))
    simpa only [Fin.val_one, pow_one] using hc
  · refine ⟨2, by norm_num, by norm_num, b, a, ?_⟩
    simp only [pow_zero, Matrix.one_mulVec]
    change ((T ^ 2).mulVec (icoVector a)) ⬝ᵥ icoVector b =
      icoVector b ⬝ᵥ ((T ^ 2).mulVec (icoVector a))
    exact dotProduct_comm _ _
  · refine ⟨1, by norm_num, by norm_num, b, a, ?_⟩
    change dot ((T ^ 2).mulVec (icoVector a)) ((T ^ 1).mulVec (icoVector b)) =
      dot (icoVector b) ((T ^ 1).mulVec (icoVector a))
    rw [pow_two, ← Matrix.mulVec_mulVec]
    have hc : dot (T.mulVec (T.mulVec (icoVector a))) (T.mulVec (icoVector b)) =
        dot (T.mulVec (icoVector a)) (icoVector b) := by
      have h := hcomm (1 : Fin 3) (T.mulVec (icoVector a)) (icoVector b)
      simpa only [Fin.val_one, pow_one] using h
    have hs : dot (T.mulVec (icoVector a)) (icoVector b) =
        dot (icoVector b) (T.mulVec (icoVector a)) := by
      change (T.mulVec (icoVector a)) ⬝ᵥ icoVector b =
        icoVector b ⬝ᵥ (T.mulVec (icoVector a))
      exact dotProduct_comm _ _
    simpa only [pow_one] using hc.trans hs
  · exact (False.elim (hij rfl))

end AKLT.W.Q007
