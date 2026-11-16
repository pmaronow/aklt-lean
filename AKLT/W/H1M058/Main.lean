import AKLT.Blueprint.H1.NodesV2Pauli

noncomputable section

open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.H1M058

private def inversionSign {n : ℕ} (I : Finset (Fin n)) (v : Fin n × Fin 3) : ℝ :=
  if v.1 ∈ I then -1 else 1

private def inversionFactor {n : ℕ} (I : Finset (Fin n)) (d : (Fin n × Fin 3) →₀ ℕ) : ℝ :=
  d.prod fun v e => inversionSign I v ^ e

private def inversionHom {n : ℕ} (I : Finset (Fin n)) :
    RealVectorPolynomial n →+* RealVectorPolynomial n :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun v => MvPolynomial.C (inversionSign I v) * MvPolynomial.X v)

private lemma inversion_eq_hom {n : ℕ} (I : Finset (Fin n)) (p : RealVectorPolynomial n) :
    invertPolynomialReal I p = inversionHom I p := by
  unfold invertPolynomialReal inversionHom
  exact MvPolynomial.eval₂Hom_congr rfl (by
    funext v
    by_cases h : v.1 ∈ I <;> simp [inversionSign, h]) rfl

private lemma invert_monomial {n : ℕ} (I : Finset (Fin n))
    (d : (Fin n × Fin 3) →₀ ℕ) (c : ℝ) :
    inversionHom I (MvPolynomial.monomial d c) =
      MvPolynomial.monomial d (c * inversionFactor I d) := by
  rw [inversionHom, MvPolynomial.eval₂Hom_monomial, MvPolynomial.monomial_eq]
  have hprod :
      d.prod (fun v e =>
        (MvPolynomial.C (inversionSign I v) * MvPolynomial.X v) ^ e) =
        MvPolynomial.C (inversionFactor I d) *
          d.prod (fun v e => MvPolynomial.X v ^ e) := by
    simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, inversionFactor,
      ← map_pow, ← map_prod]
  rw [hprod]
  calc
    MvPolynomial.C c *
        (MvPolynomial.C (inversionFactor I d) * d.prod (fun v e => MvPolynomial.X v ^ e)) =
      (MvPolynomial.C c * MvPolynomial.C (inversionFactor I d)) *
        d.prod (fun v e => MvPolynomial.X v ^ e) := by ac_rfl
    _ = MvPolynomial.C (c * inversionFactor I d) *
        d.prod (fun v e => MvPolynomial.X v ^ e) := by rw [← map_mul]

private lemma invert_as_sum {n : ℕ} (I : Finset (Fin n)) (p : RealVectorPolynomial n) :
    inversionHom I p =
      ∑ d ∈ p.support, MvPolynomial.monomial d (p.coeff d * inversionFactor I d) := by
  conv_lhs => rw [MvPolynomial.as_sum p]
  simp only [map_sum, invert_monomial]

private lemma invert_support_subset {n : ℕ} (I : Finset (Fin n))
    (p : RealVectorPolynomial n) : (inversionHom I p).support ⊆ p.support := by
  rw [invert_as_sum]
  refine MvPolynomial.support_sum.trans (Finset.biUnion_subset.mpr fun d hd => ?_)
  rw [MvPolynomial.support_monomial]
  split_ifs <;> simp [hd]

private lemma eval_inversion_hom {n : ℕ} (I : Finset (Fin n)) (u : Fin n → Vec3)
    (p : RealVectorPolynomial n) :
    evaluateRealPolynomial (inversionHom I p) (invertVectorsReal I u) =
      evaluateRealPolynomial p u := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [evaluateRealPolynomial, inversionHom]
  | add p q hp hq =>
      change MvPolynomial.eval (fun v => invertVectorsReal I u v.1 v.2)
          (inversionHom I (p + q)) = MvPolynomial.eval (fun v => u v.1 v.2) (p + q)
      rw [map_add, MvPolynomial.eval_add, MvPolynomial.eval_add]
      change MvPolynomial.eval (fun v => invertVectorsReal I u v.1 v.2) (inversionHom I p) +
          MvPolynomial.eval (fun v => invertVectorsReal I u v.1 v.2) (inversionHom I q) =
        MvPolynomial.eval (fun v => u v.1 v.2) p + MvPolynomial.eval (fun v => u v.1 v.2) q
      change MvPolynomial.eval (fun w => invertVectorsReal I u w.1 w.2)
          (inversionHom I p) = MvPolynomial.eval (fun w => u w.1 w.2) p at hp
      change MvPolynomial.eval (fun w => invertVectorsReal I u w.1 w.2)
          (inversionHom I q) = MvPolynomial.eval (fun w => u w.1 w.2) q at hq
      rw [hp, hq]
  | mul_X p v hp =>
      change MvPolynomial.eval (fun v => invertVectorsReal I u v.1 v.2)
          (inversionHom I (p * MvPolynomial.X v)) =
        MvPolynomial.eval (fun v => u v.1 v.2) (p * MvPolynomial.X v)
      rw [map_mul, MvPolynomial.eval_mul, MvPolynomial.eval_mul]
      change MvPolynomial.eval (fun v => invertVectorsReal I u v.1 v.2) (inversionHom I p) *
          MvPolynomial.eval (fun v => invertVectorsReal I u v.1 v.2) (inversionHom I (MvPolynomial.X v)) =
        MvPolynomial.eval (fun v => u v.1 v.2) p *
          MvPolynomial.eval (fun v => u v.1 v.2) (MvPolynomial.X v)
      change MvPolynomial.eval (fun w => invertVectorsReal I u w.1 w.2)
          (inversionHom I p) = MvPolynomial.eval (fun w => u w.1 w.2) p at hp
      rw [hp]
      have hv : MvPolynomial.eval (fun w => invertVectorsReal I u w.1 w.2)
          (inversionHom I (MvPolynomial.X v)) = u v.1 v.2 := by
        by_cases h : v.1 ∈ I <;> simp [inversionHom, inversionSign, invertVectorsReal, h]
      rw [hv]
      simp [MvPolynomial.eval_X]

theorem main : AKLT.Blueprint.H1.InversionPolynomialStatementV2 := by
  classical
  intro n J I p hAffine hSupport
  have hsupport : (invertPolynomialReal I p).support ⊆ p.support := by
    rw [inversion_eq_hom]
    exact invert_support_subset I p
  refine ⟨?_, ?_, ?_⟩
  · intro d hd j
    exact hAffine d (hsupport hd) j
  · intro d hd j hj k
    exact hSupport d (hsupport hd) j hj k
  · intro u
    rw [inversion_eq_hom]
    exact eval_inversion_hom I u p

end AKLT.W.H1M058
