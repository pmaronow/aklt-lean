module
public import AKLT.Blueprint.H1.NodesStructure
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Derivative

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators

namespace AKLT.W.H1M049

open AKLT.Defs AKLT.Blueprint.H1

private def slotPoly (J : Finset (Fin 20)) (A : Matrix (Fin 2) (Fin 2) ℂ)
    (σ τ : J → Fin 2) (j : J) : Polynomial ℂ :=
  Polynomial.C (if σ j = τ j then 1 else 0) +
    Polynomial.X * Polynomial.C (A (σ j) (τ j))

private def tensorPoly (J : Finset (Fin 20)) (A : Matrix (Fin 2) (Fin 2) ℂ)
    (σ τ : J → Fin 2) : Polynomial ℂ :=
  ∏ j : J, slotPoly J A σ τ j

private def commutatorPoly (J : Finset (Fin 20)) (M : Matrix (J → Fin 2) (J → Fin 2) ℂ)
    (A : Matrix (Fin 2) (Fin 2) ℂ) (σ τ : J → Fin 2) : Polynomial ℂ :=
  (∑ ρ : J → Fin 2, Polynomial.C (M σ ρ) * tensorPoly J A ρ τ) -
    (∑ ρ : J → Fin 2, tensorPoly J A σ ρ * Polynomial.C (M ρ τ))

private lemma deltaProd (α : Type*) [DecidableEq α] (s : Finset α) (f g : α → Fin 2) :
    (∏ k ∈ s, if f k = g k then (1 : ℂ) else 0) =
      if ∀ k ∈ s, f k = g k then 1 else 0 := by
  classical
  by_cases h : ∀ k ∈ s, f k = g k
  · rw [if_pos h]
    apply Finset.prod_eq_one
    intro k hk
    simp [h k hk]
  · have hn := h
    push Not at h
    obtain ⟨k, hk, hne⟩ := h
    rw [if_neg hn]
    rw [Finset.prod_eq_zero hk (by simp [hne])]

private lemma tensorPoly_derivative_eval_zero
    (J : Finset (Fin 20)) (A : Matrix (Fin 2) (Fin 2) ℂ) (σ τ : J → Fin 2) :
    (tensorPoly J A σ τ).derivative.eval 0 =
      ∑ j : J, tokenMatrix J j A σ τ := by
  classical
  unfold tensorPoly
  rw [Polynomial.derivative_prod_finset]
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul]
  simp only [slotPoly, Polynomial.eval_prod, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.derivative_add, Polynomial.derivative_C,
    Polynomial.derivative_mul, Polynomial.derivative_X]
  simp only [zero_mul, add_zero, one_mul]
  simp_rw [deltaProd]
  simp [tokenMatrix, Finset.mem_erase, Finset.mem_univ]

theorem main : AKLT.Blueprint.H1.TensorLinearCoefficientStatement := by
  classical
  intro J M A hcomm
  let S : Matrix (J → Fin 2) (J → Fin 2) ℂ := ∑ j : J, tokenMatrix J j A
  apply Matrix.ext
  intro σ τ
  let q := commutatorPoly J M A σ τ
  have hroots : Set.Infinite {z : ℂ | q.IsRoot z} := by
    have hrange : Set.Infinite (Set.range fun t : ℝ => (t : ℂ)) :=
      Set.infinite_range_of_injective (fun x y hxy => by exact_mod_cast hxy)
    apply hrange.mono
    rintro z ⟨t, rfl⟩
    change q.eval (t : ℂ) = 0
    have h := hcomm t
    change M * tensorPowerMatrix J (1 + (t : ℂ) • A) =
      tensorPowerMatrix J (1 + (t : ℂ) • A) * M at h
    have heval : ∀ x y : J → Fin 2,
        (tensorPoly J A x y).eval (t : ℂ) =
          tensorPowerMatrix J (1 + (t : ℂ) • A) x y := by
      intro x y
      have hslot (j : J) :
          (slotPoly J A x y j).eval (t : ℂ) =
            (1 + (t : ℂ) • A) (x j) (y j) := by
        unfold slotPoly
        rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
          Polynomial.eval_X, Polynomial.eval_C]
        simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply]
        ring
      simp only [tensorPoly, tensorPowerMatrix, Polynomial.eval_prod]
      exact Finset.prod_congr rfl (fun j hj => hslot j)
    have hqEval : q.eval (t : ℂ) =
        (M * tensorPowerMatrix J (1 + (t : ℂ) • A)) σ τ -
          (tensorPowerMatrix J (1 + (t : ℂ) • A) * M) σ τ := by
      simp [q, commutatorPoly, Polynomial.eval_sub, Polynomial.eval_finsetSum,
        Polynomial.eval_mul, Polynomial.eval_C, heval, Matrix.mul_apply]
    rw [hqEval]
    exact sub_eq_zero.mpr (congrArg (fun B : Matrix (J → Fin 2) (J → Fin 2) ℂ => B σ τ) h)
  have hq : q = 0 := Polynomial.eq_zero_of_infinite_isRoot q hroots
  have hderiv : q.derivative.eval 0 = 0 := by simp [hq]
  have hlinear := tensorPoly_derivative_eval_zero J A
  have hlinear' : ∀ x y : J → Fin 2,
      (tensorPoly J A x y).derivative.eval 0 = S x y := by
    intro x y
    simpa [S, Matrix.sum_apply] using hlinear x y
  have hentry : (M * S) σ τ = (S * M) σ τ := by
    have hqDeriv : q.derivative.eval 0 = (M * S) σ τ - (S * M) σ τ := by
      simp [q, commutatorPoly, Polynomial.derivative_sub, Polynomial.derivative_sum,
        Polynomial.derivative_mul, Polynomial.derivative_C, Polynomial.eval_sub,
        Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
        Matrix.mul_apply, hlinear']
    rw [hqDeriv] at hderiv
    exact sub_eq_zero.mp hderiv
  exact hentry

end AKLT.W.H1M049
