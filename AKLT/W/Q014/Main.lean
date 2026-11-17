module
public import AKLT.Blueprint.Q.NodesTight

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators

namespace AKLT.W.Q014

open AKLT.Defs AKLT.Blueprint.Q

theorem main : AKLT.Blueprint.Q.ResolutionExpansionStatement := by
  classical
  intro A inst w z hres p
  let m : Fin 5 → A → ℂ := fun j a => quarticMonomial j (z a)
  have hexpand (a : A) :
      (Complex.normSq (binaryEval 4 p (z a)) : ℂ) =
        ∑ j : Fin 5, ∑ k : Fin 5,
          (star (p j) * p k) * (star (m j a) * m k a) := by
    rw [Complex.normSq_eq_conj_mul_self]
    simp only [binaryEval, m, map_sum, map_mul]
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    simp [quarticMonomial]
    ring_nf
  have hC :
      (∑ a : A, (5 * w a : ℂ) * (Complex.normSq (binaryEval 4 p (z a)) : ℂ)) =
        (binaryNormSq 4 p : ℂ) := by
   calc
    (∑ a : A, (5 * w a : ℂ) * (Complex.normSq (binaryEval 4 p (z a)) : ℂ)) =
        ∑ a : A, (5 * w a : ℂ) *
          ∑ j : Fin 5, ∑ k : Fin 5,
            (star (p j) * p k) * (star (m j a) * m k a) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [hexpand]
    _ = ∑ j : Fin 5, ∑ k : Fin 5,
          (star (p j) * p k) *
            ∑ a : A, (5 * w a : ℂ) * (star (m j a) * m k a) := by
      simp_rw [Finset.mul_sum]
      simp_rw [show ∀ a j k, (5 * w a : ℂ) *
          ((star (p j) * p k) * (star (m j a) * m k a)) =
          (star (p j) * p k) * ((5 * w a : ℂ) * (star (m j a) * m k a))
        from fun _ _ _ => by ring]
      rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
        (f := fun a j => ∑ k : Fin 5,
          (star (p j) * p k) * ((5 * w a : ℂ) * (star (m j a) * m k a)))]
      simp_rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
        (f := fun a k => (star (p _) * p k) * ((5 * w a : ℂ) * (star (m _ a) * m k a)))]
    _ = ∑ j : Fin 5, ∑ k : Fin 5,
          (star (p j) * p k) * (if j = k then (Nat.choose 4 j.val : ℂ)⁻¹ else 0) := by
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      simpa [m, mul_assoc] using
        congrArg (fun q : ℂ => (star (p j) * p k) * q) (hres j k)
    _ = ∑ j : Fin 5,
          (star (p j) * p j) * (Nat.choose 4 j.val : ℂ)⁻¹ := by
      simp
    _ = (binaryNormSq 4 p : ℂ) := by
      simp [binaryNormSq, Complex.normSq_eq_conj_mul_self, div_eq_mul_inv]
  exact_mod_cast hC

end AKLT.W.Q014
