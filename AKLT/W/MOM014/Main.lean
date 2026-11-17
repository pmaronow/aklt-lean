import AKLT.Blueprint.Mom.NodesFinite

noncomputable section
open scoped BigOperators

namespace AKLT.W.MOM014

private def HasNonnegCoeffs {σ : Type*} (p : MvPolynomial σ ℝ) : Prop :=
  ∀ m, 0 ≤ p.coeff m

private theorem hasNonnegCoeffs_one {σ : Type*} [DecidableEq σ] :
    HasNonnegCoeffs (1 : MvPolynomial σ ℝ) := by
  intro m
  rw [MvPolynomial.coeff_one]
  split_ifs <;> norm_num

private theorem hasNonnegCoeffs_X {σ : Type*} [DecidableEq σ] (x : σ) :
    HasNonnegCoeffs (MvPolynomial.X x : MvPolynomial σ ℝ) := by
  intro m
  rw [MvPolynomial.coeff_X]
  split_ifs <;> norm_num

private theorem hasNonnegCoeffs_add {σ : Type*}
    {p q : MvPolynomial σ ℝ}
    (hp : HasNonnegCoeffs p) (hq : HasNonnegCoeffs q) :
    HasNonnegCoeffs (p + q) := by
  intro m
  rw [AddMonoidAlgebra.coeff_add]
  change 0 ≤ p.coeff m + q.coeff m
  exact add_nonneg (hp m) (hq m)

private theorem hasNonnegCoeffs_mul {σ : Type*} [DecidableEq σ]
    {p q : MvPolynomial σ ℝ}
    (hp : HasNonnegCoeffs p) (hq : HasNonnegCoeffs q) :
    HasNonnegCoeffs (p * q) := by
  intro m
  rw [MvPolynomial.coeff_mul]
  apply Finset.sum_nonneg
  intro a ha
  exact mul_nonneg (hp a.1) (hq a.2)

private theorem hasNonnegCoeffs_finset_prod {α σ : Type*} [DecidableEq α]
    [DecidableEq σ] (s : Finset α) (f : α → MvPolynomial σ ℝ)
    (hf : ∀ a ∈ s, HasNonnegCoeffs (f a)) :
    HasNonnegCoeffs (∏ a ∈ s, f a) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using (hasNonnegCoeffs_one (σ := σ))
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha]
      apply hasNonnegCoeffs_mul
      · exact hf a (Finset.mem_insert_self a s)
      · apply ih
        intro b hb
        exact hf b (Finset.mem_insert_of_mem hb)

private theorem hasNonnegCoeffs_observableList {n : ℕ}
    (pairs : List (Fin n × Fin n)) :
    HasNonnegCoeffs ((pairs.map AKLT.Blueprint.Mom.dotPolynomial).prod) := by
  classical
  induction pairs with
  | nil =>
      simpa using (hasNonnegCoeffs_one (σ := Fin n × Fin 3))
  | cons e es ih =>
      simp only [List.map_cons, List.prod_cons]
      apply hasNonnegCoeffs_mul
      · unfold HasNonnegCoeffs
        intro m
        unfold AKLT.Blueprint.Mom.dotPolynomial
        rw [MvPolynomial.coeff_sum]
        apply Finset.sum_nonneg
        intro i hi
        exact hasNonnegCoeffs_mul
          (hasNonnegCoeffs_X (σ := Fin n × Fin 3) (e.1, i))
          (hasNonnegCoeffs_X (σ := Fin n × Fin 3) (e.2, i)) m
      · exact ih

private theorem hasNonnegCoeffs_bondFactor {n : ℕ}
    (e : Fin n × Fin n) :
    HasNonnegCoeffs (1 + AKLT.Blueprint.Mom.dotPolynomial e) := by
  apply hasNonnegCoeffs_add
  · exact hasNonnegCoeffs_one
  · unfold HasNonnegCoeffs
    intro m
    unfold AKLT.Blueprint.Mom.dotPolynomial
    rw [MvPolynomial.coeff_sum]
    apply Finset.sum_nonneg
    intro i hi
    exact hasNonnegCoeffs_mul
      (hasNonnegCoeffs_X (σ := Fin n × Fin 3) (e.1, i))
      (hasNonnegCoeffs_X (σ := Fin n × Fin 3) (e.2, i)) m

theorem main : AKLT.Blueprint.Mom.FreeCoefficientsStatement := by
  classical
  intro n D pairs m
  change 0 ≤
    ((∏ e ∈ D.bonds, (1 + AKLT.Blueprint.Mom.dotPolynomial e)) *
      (pairs.map AKLT.Blueprint.Mom.dotPolynomial).prod).coeff m
  apply hasNonnegCoeffs_mul
  · exact hasNonnegCoeffs_finset_prod D.bonds
      (fun e => 1 + AKLT.Blueprint.Mom.dotPolynomial e)
      (fun e he => hasNonnegCoeffs_bondFactor e)
  · exact hasNonnegCoeffs_observableList pairs
  
end AKLT.W.MOM014
