import AKLT.Blueprint.Mom.NodesCore

noncomputable section
open scoped BigOperators

namespace AKLT.W.MOM010

open AKLT.Blueprint.Mom
open AKLT.Defs

private theorem exponentProduct_eq {n : ℕ} (m : Fin n × Fin 3 →₀ ℕ)
    (a : Fin n → Vec3) :
    (∏ z : Fin n × Fin 3, (a z.1 z.2) ^ m z) =
      ∏ x : Fin n, mono (fun i => m (x, i)) (a x) := by
  classical
  simp only [mono]
  rw [← Finset.prod_product (Finset.univ : Finset (Fin n))
    (Finset.univ : Finset (Fin 3)) (fun z : Fin n × Fin 3 => (a z.1 z.2) ^ m z)]
  simp

theorem main : AKLT.Blueprint.Mom.PolynomialExpansionStatement := by
  classical
  intro n α _ w v p
  unfold AKLT.Blueprint.Mom.productSum
  calc
    (∑ b : (x : Fin n) → α x,
        (∏ x, w x (b x)) *
          MvPolynomial.eval (fun z => v z.1 (b z.1) z.2) p) =
      ∑ b : (x : Fin n) → α x,
        ∑ m ∈ p.support, p.coeff m *
          ((∏ x, w x (b x)) *
            ∏ x, mono (fun i => m (x, i)) (v x (b x))) := by
      simp only [MvPolynomial.eval_eq']
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro m hm
      rw [exponentProduct_eq (a := fun x => v x (b x))]
      ring
    _ = ∑ m ∈ p.support, ∑ b : (x : Fin n) → α x,
        p.coeff m *
          ((∏ x, w x (b x)) *
            ∏ x, mono (fun i => m (x, i)) (v x (b x))) := by
      rw [Finset.sum_comm]
    _ = ∑ m ∈ p.support, p.coeff m *
        (∑ b : (x : Fin n) → α x,
          (∏ x, w x (b x)) *
            ∏ x, mono (fun i => m (x, i)) (v x (b x))) := by
      apply Finset.sum_congr rfl
      intro m hm
      simp only [Finset.mul_sum]

end AKLT.W.MOM010

#print axioms AKLT.W.MOM010.main
