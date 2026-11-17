module
public import AKLT.Blueprint.H1.NodesStructure

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.H1M041

private theorem pauli_conj_entry (a : Fin 4) (i j : Fin 2) :
    star (pauli a j i) = pauli a i j := by
  fin_cases a <;> fin_cases i <;> fin_cases j <;> simp [pauli]

theorem main : AKLT.Blueprint.H1.PauliHermitianStatement := by
  intro J p
  rw [Matrix.IsHermitian.ext_iff]
  intro σ τ
  change star (∑ a : J → Fin 4,
      (↑(p.coeff (pauliExponent J a)) : ℂ) * ∏ j : J, pauli (a j) (τ j) (σ j)) =
    ∑ a : J → Fin 4,
      (↑(p.coeff (pauliExponent J a)) : ℂ) * ∏ j : J, pauli (a j) (σ j) (τ j)
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [star_mul, star_prod]
  rw [show star (↑(p.coeff (pauliExponent J a)) : ℂ) =
    (↑(p.coeff (pauliExponent J a)) : ℂ) by simp]
  rw [mul_comm]
  apply congrArg (fun z : ℂ => (↑(p.coeff (pauliExponent J a)) : ℂ) * z)
  apply Finset.prod_congr rfl
  intro j hj
  exact pauli_conj_entry (a j) (σ j) (τ j)

end AKLT.W.H1M041

#print axioms AKLT.W.H1M041.main
