module
public import AKLT.Blueprint.Q.NodesPolynomial

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section

open scoped BigOperators
open AKLT.Defs AKLT.Challenge AKLT.Blueprint.Q

namespace AKLT.W.Q021

theorem main : AKLT.Blueprint.Q.StateEvaluationStatement := by
  intro L N ψ z
  classical
  unfold statePolynomial physicalEval
  simp only [MvPolynomial.eval_sum, MvPolynomial.eval_mul, MvPolynomial.eval_C,
    MvPolynomial.eval_monomial]
  apply Finset.sum_congr rfl
  intro σ hσ
  let s : Site L N → ℂ := fun x =>
    (Real.sqrt (Nat.choose 4 (σ x).val : ℝ) : ℂ)
  let p : Site L N → ℂ := fun x =>
    z x 0 ^ (4 - (σ x).val) * z x 1 ^ (σ x).val
  have hdeg : (monomialDegree σ).prod (fun v e => z v.1 v.2 ^ e) =
      ∏ x : Site L N, p x := by
    simp [p, monomialDegree, Fintype.prod_prod_type, Fin.prod_univ_two]
  rw [hdeg]
  have hprod : (∏ x : Site L N, s x * p x) =
      (∏ x : Site L N, s x) * (∏ x : Site L N, p x) := by
    simpa using (Finset.prod_mul_distrib
      (s := (Finset.univ : Finset (Site L N))) (f := s) (g := p))
  simp only [one_mul]
  calc
    (ψ σ * (∏ x : Site L N, s x)) * (∏ x : Site L N, p x) =
        ψ σ * ((∏ x : Site L N, s x) * (∏ x : Site L N, p x)) := by ring
    _ = ψ σ * (∏ x : Site L N, s x * p x) := by rw [← hprod]
    _ = ψ σ * (∏ x : Site L N,
        (Real.sqrt (Nat.choose 4 (σ x).val : ℝ) : ℂ) *
          z x 0 ^ (4 - (σ x).val) * z x 1 ^ (σ x).val) := by
      congr 1
      apply Finset.prod_congr rfl
      intro x hx
      simp only [s, p]
      ring

end AKLT.W.Q021
