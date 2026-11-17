module
public import AKLT.Blueprint.Q.NodesTight

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section

open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Q

namespace AKLT.W.Q011

def realPartPolynomial (p : MvPolynomial (Fin 3) ℂ) : MvPolynomial (Fin 3) ℝ :=
  ∑ m ∈ p.support, MvPolynomial.monomial m (p.coeff m).re

def imagPartPolynomial (p : MvPolynomial (Fin 3) ℂ) : MvPolynomial (Fin 3) ℝ :=
  ∑ m ∈ p.support, MvPolynomial.monomial m (p.coeff m).im

lemma realPartPolynomial_degree (p : MvPolynomial (Fin 3) ℂ) :
    (realPartPolynomial p).totalDegree ≤ p.totalDegree := by
  classical
  rw [realPartPolynomial]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro m hm
  exact (MvPolynomial.totalDegree_monomial_le m _).trans (MvPolynomial.le_totalDegree hm)

lemma imagPartPolynomial_degree (p : MvPolynomial (Fin 3) ℂ) :
    (imagPartPolynomial p).totalDegree ≤ p.totalDegree := by
  classical
  rw [imagPartPolynomial]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro m hm
  exact (MvPolynomial.totalDegree_monomial_le m _).trans (MvPolynomial.le_totalDegree hm)

lemma ofReal_weightedSum {A : Type*} [Fintype A] (w f : A → ℝ) :
    ((∑ a, w a * f a : ℝ) : ℂ) = ∑ a, (w a : ℂ) * (f a : ℂ) := by
  classical
  simpa [Complex.ofReal_mul] using
    (map_sum Complex.ofRealHom (fun a => w a * f a) Finset.univ)

lemma eval_complex_eq_parts (p : MvPolynomial (Fin 3) ℂ) (x : Vec3) :
    MvPolynomial.eval (fun i => (x i : ℂ)) p =
      ((MvPolynomial.eval x (realPartPolynomial p) : ℝ) : ℂ) +
        Complex.I * ((MvPolynomial.eval x (imagPartPolynomial p) : ℝ) : ℂ) := by
  classical
  conv_lhs => rw [p.as_sum]
  simp only [realPartPolynomial, imagPartPolynomial, MvPolynomial.eval_sum,
    MvPolynomial.eval_monomial]
  simp only [Complex.ofReal_sum, Complex.ofReal_mul]
  simp only [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  calc
    p.coeff m * (∏ n ∈ m.support, (x n : ℂ) ^ m n) =
        ((p.coeff m).re + (p.coeff m).im * Complex.I) *
          (∏ n ∈ m.support, (x n : ℂ) ^ m n) := by rw [Complex.re_add_im]
    _ = _ := by
      have hprod : (∏ n ∈ m.support, (x n : ℂ) ^ m n) =
          ((m.prod fun n e => x n ^ e : ℝ) : ℂ) := by
        simpa [Finsupp.prod, Complex.ofReal_pow] using
          (map_finsuppProd Complex.ofRealHom m (fun n e => x n ^ e)).symm
      rw [hprod]
      ring

lemma weighted_eval_parts {A : Type*} [Fintype A] (v : A → Vec3) (w : A → ℝ)
    (p : MvPolynomial (Fin 3) ℂ) :
    (∑ a, (w a : ℂ) * MvPolynomial.eval (fun i => (v a i : ℂ)) p) =
      ((∑ a, w a * MvPolynomial.eval (v a) (realPartPolynomial p) : ℝ) : ℂ) +
        Complex.I * ((∑ a, w a * MvPolynomial.eval (v a) (imagPartPolynomial p) : ℝ) : ℂ) := by
  classical
  calc
    (∑ a, (w a : ℂ) * MvPolynomial.eval (fun i => (v a i : ℂ)) p) =
        (∑ a, (w a : ℂ) *
            ((MvPolynomial.eval (v a) (realPartPolynomial p) : ℝ) : ℂ)) +
          ∑ a, (w a : ℂ) *
            (Complex.I * ((MvPolynomial.eval (v a) (imagPartPolynomial p) : ℝ) : ℂ)) := by
      simp_rw [eval_complex_eq_parts, mul_add]
      exact Finset.sum_add_distrib
    _ = _ := by
      rw [ofReal_weightedSum, ofReal_weightedSum]
      rw [Finset.mul_sum Finset.univ
        (fun a => (w a : ℂ) * ((MvPolynomial.eval (v a) (imagPartPolynomial p) : ℝ) : ℂ))
        Complex.I]
      congr 1
      apply Finset.sum_congr rfl
      intro a ha
      ring

lemma complexMoment_parts (p : MvPolynomial (Fin 3) ℂ) :
    complexMoment p =
      ((AKLT.Defs.moment (fun u => MvPolynomial.eval u (realPartPolynomial p))) : ℝ) +
        Complex.I *
          ((AKLT.Defs.moment (fun u => MvPolynomial.eval u (imagPartPolynomial p))) : ℝ) := by
  simpa [complexMoment, AKLT.Defs.moment, Finset.mul_sum] using
    (weighted_eval_parts (v := icoVector) (w := fun _ => (1 / 12 : ℝ)) p)

theorem main : AKLT.Blueprint.Q.ComplexQuadratureStatement := by
  classical
  intro A instA v w hquad p hp
  let pr := realPartPolynomial p
  let pi := imagPartPolynomial p
  have hpr : DegreeFour pr := (realPartPolynomial_degree p).trans hp
  have hpi : DegreeFour pi := (imagPartPolynomial_degree p).trans hp
  have hqr := hquad pr hpr
  have hqi := hquad pi hpi
  rw [weighted_eval_parts, complexMoment_parts, hqr, hqi]

end AKLT.W.Q011
