module
public import AKLT.Blueprint.H1.NodesV2Pauli

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.H1M057

private theorem sum_pi_prod {ι : Type*} [Fintype ι] [DecidableEq ι]
    (β : ι → Type*) [∀ i, Fintype (β i)]
    (f : ∀ i, β i → ℂ) :
    (∑ x : ∀ i, β i, ∏ i, f i (x i)) = ∏ i, ∑ b : β i, f i b := by
  classical
  exact (Fintype.prod_sum (κ := β) (f := f)).symm

private theorem sum_comm2 {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β → ℂ) : (∑ a, ∑ b, f a b) = ∑ b, ∑ a, f a b := by
  classical
  exact Finset.sum_comm (f := f) (s := (Finset.univ : Finset α))
    (t := (Finset.univ : Finset β))

private theorem tensor_trace_factor {n : ℕ} (J : Finset (Fin n))
    (u : Fin n → Vec3) (a : J → Fin 4)
    (hslot : ∀ a : Fin 4, ∀ v : Vec3,
      (pauli a * spinDensity v).trace = (AKLT.Blueprint.H1.pauliCoordinate v a : ℂ)) :
    (∑ σ : J → Fin 2, ∑ τ : J → Fin 2,
      ∏ j : J, pauli (a j) (σ j) (τ j) * spinDensity (u j.val) (τ j) (σ j)) =
      ∏ j : J, (AKLT.Blueprint.H1.pauliCoordinate (u j.val) (a j) : ℂ) := by
  classical
  calc
    (∑ σ : J → Fin 2, ∑ τ : J → Fin 2,
        ∏ j : J, pauli (a j) (σ j) (τ j) * spinDensity (u j.val) (τ j) (σ j))
        = ∑ σ : J → Fin 2, ∏ j : J,
            ∑ t : Fin 2, pauli (a j) (σ j) t * spinDensity (u j.val) t (σ j) := by
          congr 1
          funext σ
          exact sum_pi_prod (fun _ : J => Fin 2) (fun j t =>
            pauli (a j) (σ j) t * spinDensity (u j.val) t (σ j))
    _ = ∏ j : J, ∑ s : Fin 2, ∑ t : Fin 2,
            pauli (a j) s t * spinDensity (u j.val) t s := by
          exact sum_pi_prod (fun _ : J => Fin 2) (fun j s => ∑ t : Fin 2,
            pauli (a j) s t * spinDensity (u j.val) t s)
    _ = ∏ j : J, (pauli (a j) * spinDensity (u j.val)).trace := by
          apply Finset.prod_congr rfl
          intro j hj
          simp [Matrix.trace, Matrix.mul_apply]
    _ = ∏ j : J, (AKLT.Blueprint.H1.pauliCoordinate (u j.val) (a j) : ℂ) := by
          apply Finset.prod_congr rfl
          intro j hj
          exact hslot (a j) (u j.val)

theorem main : AKLT.Blueprint.H1.PauliProductTraceStatementV2 := by
  intro hslot n J p u
  classical
  have hExpand :
      (pauliOperatorReal J p * productDensityReal J u).trace =
        ∑ a : J → Fin 4,
          (p.coeff (pauliExponentReal J a) : ℂ) *
            (∑ σ : J → Fin 2, ∑ τ : J → Fin 2,
              ∏ j : J, pauli (a j) (σ j) (τ j) *
                spinDensity (u j.val) (τ j) (σ j)) := by
    change (∑ σ : J → Fin 2, ∑ τ : J → Fin 2,
        (∑ a : J → Fin 4,
          (p.coeff (pauliExponentReal J a) : ℂ) *
            ∏ j : J, pauli (a j) (σ j) (τ j)) *
          ∏ j : J, spinDensity (u j.val) (τ j) (σ j)) = _
    calc
      (∑ σ : J → Fin 2, ∑ τ : J → Fin 2,
          (∑ a : J → Fin 4,
            (p.coeff (pauliExponentReal J a) : ℂ) *
              ∏ j : J, pauli (a j) (σ j) (τ j)) *
            ∏ j : J, spinDensity (u j.val) (τ j) (σ j))
          = ∑ σ : J → Fin 2, ∑ τ : J → Fin 2, ∑ a : J → Fin 4,
              (p.coeff (pauliExponentReal J a) : ℂ) *
                (∏ j : J, pauli (a j) (σ j) (τ j) *
                  spinDensity (u j.val) (τ j) (σ j)) := by
            simp_rw [Finset.sum_mul, mul_assoc, ← Finset.prod_mul_distrib]
      _ = ∑ σ : J → Fin 2, ∑ a : J → Fin 4, ∑ τ : J → Fin 2,
              (p.coeff (pauliExponentReal J a) : ℂ) *
                (∏ j : J, pauli (a j) (σ j) (τ j) *
                  spinDensity (u j.val) (τ j) (σ j)) := by
            apply Finset.sum_congr rfl
            intro σ hσ
            exact sum_comm2 (α := J → Fin 2) (β := J → Fin 4) (fun τ a =>
              (p.coeff (pauliExponentReal J a) : ℂ) *
                ∏ j : J, pauli (a j) (σ j) (τ j) * spinDensity (u j.val) (τ j) (σ j))
      _ = ∑ a : J → Fin 4, ∑ σ : J → Fin 2, ∑ τ : J → Fin 2,
              (p.coeff (pauliExponentReal J a) : ℂ) *
                (∏ j : J, pauli (a j) (σ j) (τ j) *
                  spinDensity (u j.val) (τ j) (σ j)) := by
            exact sum_comm2 (α := J → Fin 2) (β := J → Fin 4) (fun σ a =>
              ∑ τ : J → Fin 2,
                (p.coeff (pauliExponentReal J a) : ℂ) *
                  ∏ j : J, pauli (a j) (σ j) (τ j) * spinDensity (u j.val) (τ j) (σ j))
      _ = ∑ a : J → Fin 4,
              (p.coeff (pauliExponentReal J a) : ℂ) *
                (∑ σ : J → Fin 2, ∑ τ : J → Fin 2,
                  ∏ j : J, pauli (a j) (σ j) (τ j) *
                    spinDensity (u j.val) (τ j) (σ j)) := by
            simp_rw [← Finset.mul_sum]
  calc
    (pauliOperatorReal J p * productDensityReal J u).trace =
        ∑ a : J → Fin 4,
          (p.coeff (pauliExponentReal J a) : ℂ) *
            (∏ j : J, (AKLT.Blueprint.H1.pauliCoordinate (u j.val) (a j) : ℂ)) := by
      rw [hExpand]
      apply Finset.sum_congr rfl
      intro a ha
      rw [tensor_trace_factor J u a hslot]
    _ = ((∑ a : J → Fin 4,
          p.coeff (pauliExponentReal J a) *
            ∏ j : J, AKLT.Blueprint.H1.pauliCoordinate (u j.val) (a j) : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum]
      apply Finset.sum_congr rfl
      intro a ha
      simp only [Complex.ofReal_mul, Complex.ofReal_prod]

end AKLT.W.H1M057

#print axioms AKLT.W.H1M057.main
