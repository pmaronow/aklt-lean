import AKLT.W.WIN052.Fiber

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Win

namespace AKLT.W.WIN052

private theorem partSum_eq_termSum (pinned : Bool) (G Y : Finset Plane)
    (τ : PinAssignment G) (f : (Plane → Vec3) → ℝ) :
    partSum pinned G Y τ f =
      ∑ n : PlaneConfiguration (G \ Y),
        partWeight pinned G Y τ n * f (extendIcoSpins n) := by
  classical
  cases pinned with
  | false =>
      simp only [partSum, Bool.false_eq_true, ite_false, freeSum]
      unfold partWeight
      simp only [Bool.false_eq_true, false_and, ite_false, Finset.prod_const_one]
      apply Finset.sum_congr rfl
      intro n hn
      ring
  | true =>
      simp only [partSum, ite_true, pinnedSum]
      unfold partWeight
      simp only [true_and]
      apply Finset.sum_congr rfl
      intro n hn
      ring

theorem main :
    AKLT.Blueprint.Win.RemovalIntegralStatement := by
  intro hM G Y τ x hstep pinned
  classical
  let e := removalConfigEquiv G Y x hstep.2.1
  rw [partSum_eq_termSum pinned G Y τ (fun _ => 1),
    partSum_eq_termSum pinned G (insert x Y) τ
      (removalPolynomial x (survivors G Y x))]
  simp only [mul_one]
  calc
    (∑ n : PlaneConfiguration (G \ Y),
        partWeight pinned G Y τ n) =
      ∑ q : PlaneConfiguration (G \ insert x Y) × IcoLetter,
        partWeight pinned G Y τ (e.symm q) := by
          apply Fintype.sum_equiv e
          intro n
          exact congrArg (fun σ => partWeight pinned G Y τ σ)
            (Equiv.symm_apply_apply e n).symm
    _ = ∑ r : PlaneConfiguration (G \ insert x Y), ∑ a : IcoLetter,
        partWeight pinned G Y τ (e.symm (r, a)) := by
          rw [Fintype.sum_prod_type]
    _ = ∑ r : PlaneConfiguration (G \ insert x Y),
        partWeight pinned G (insert x Y) τ r *
          removalPolynomial x (survivors G Y x) (extendIcoSpins r) := by
          apply Finset.sum_congr rfl
          intro r hr
          simpa [e] using siteFiber hM G Y τ x hstep pinned r
    _ = ∑ r : PlaneConfiguration (G \ insert x Y),
        partWeight pinned G (insert x Y) τ r *
          removalPolynomial x (survivors G Y x) (extendIcoSpins r) := rfl

end AKLT.W.WIN052

#print axioms AKLT.W.WIN052.main
