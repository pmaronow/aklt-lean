import AKLT.Blueprint.Win.NodesCut

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.WIN064

/-- A product of uniform, twelve-letter site laws. -/
def quadrature {ι : Type*} [Fintype ι] (v : ι → IcoLetter → Vec3)
    (p : MvPolynomial (ι × Fin 3) ℝ) : ℝ := by
  classical
  exact ∑ σ : ι → IcoLetter, (∏ _x : ι, (1 / 12 : ℝ)) *
    MvPolynomial.eval (fun z => v z.1 (σ z.1) z.2) p

/-- Expansion of a finite product quadrature into separate site monomials. -/
lemma quadrature_expand {ι : Type*} [Fintype ι]
    (v : ι → IcoLetter → Vec3) (p : MvPolynomial (ι × Fin 3) ℝ) :
    quadrature v p = ∑ m ∈ p.support, p.coeff m *
      ∏ x : ι, ((1 / 12 : ℝ) * ∑ a : IcoLetter, ∏ i : Fin 3, v x a i ^ m (x, i)) := by
  classical
  have hmono (σ : ι → IcoLetter) (m : (ι × Fin 3) →₀ ℕ) :
      (∏ z : ι × Fin 3, v z.1 (σ z.1) z.2 ^ m z) =
        ∏ x : ι, ∏ i : Fin 3, v x (σ x) i ^ m (x, i) := by
    rw [Fintype.prod_prod_type]
  unfold quadrature
  simp only [MvPolynomial.eval_eq', Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  simp only [hmono]
  calc
    (∑ σ : ι → IcoLetter, (∏ _x : ι, (1 / 12 : ℝ)) *
        (p.coeff m * ∏ x : ι, ∏ i : Fin 3, v x (σ x) i ^ m (x, i))) =
        p.coeff m * ∑ σ : ι → IcoLetter,
          ∏ x : ι, ((1 / 12 : ℝ) * ∏ i : Fin 3, v x (σ x) i ^ m (x, i)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ hσ
      rw [Finset.prod_mul_distrib]
      ring
    _ = _ := by
      congr 1
      exact (Fintype.prod_sum
        (fun x : ι => fun a : IcoLetter =>
          (1 / 12 : ℝ) * ∏ i : Fin 3, v x a i ^ m (x, i))).symm

lemma frame_monomial (hThree : AKLT.Blueprint.Top.ThreeFramesStatement)
    (j : Fin 3) (m : Fin 3 → ℕ) (hm : (∑ i, m i) ≤ 4) :
    (1 / 12 : ℝ) * (∑ a : IcoLetter, ∏ i : Fin 3, frameVector j a i ^ m i) =
      (1 / 12 : ℝ) * (∑ a : IcoLetter, ∏ i : Fin 3, icoVector a i ^ m i) := by
  let p : MvPolynomial (Fin 3) ℝ :=
    MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm m) 1
  have hp : DegreeFour p := by
    change (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm m) (1 : ℝ)).totalDegree ≤ 4
    rw [MvPolynomial.totalDegree_monomial _ (by norm_num : (1 : ℝ) ≠ 0)]
    rw [Finsupp.equivFunOnFinite_symm_sum]
    exact hm
  have heval (a : Vec3) : MvPolynomial.eval a p = ∏ i : Fin 3, a i ^ m i := by
    simp [p, MvPolynomial.eval_monomial, Finsupp.equivFunOnFinite_symm_apply_apply]
  have h := (hThree.2.2.2.2.2.2.1 j).2.2.2 p hp
  simpa only [heval, moment] using h

/-- Only the supplied single-site polynomial identities are needed for transfer. -/
theorem frame_quadrature {ι : Type*} [Fintype ι]
    (hThree : AKLT.Blueprint.Top.ThreeFramesStatement) (κ : ι → Fin 3)
    (p : MvPolynomial (ι × Fin 3) ℝ) (hp : SeparateDegreeFour p) :
    quadrature (fun x => frameVector (κ x)) p = quadrature (fun _ => icoVector) p := by
  classical
  rw [quadrature_expand, quadrature_expand]
  apply Finset.sum_congr rfl
  intro m hm
  congr 1
  apply Finset.prod_congr rfl
  intro x hx
  exact frame_monomial hThree (κ x) (fun i => m (x, i)) (hp m hm x)

#print axioms quadrature_expand
#print axioms frame_monomial
#print axioms frame_quadrature

end AKLT.W.WIN064
