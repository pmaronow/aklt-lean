import AKLT.Blueprint.H1.NodesStructure

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.H1

namespace AKLT.W.H1M043

private theorem pauli_entry_conj (a : Fin 4) (i j : Fin 2) :
    star (pauli a i j) = if a = 2 then -pauli a i j else pauli a i j := by
  fin_cases a <;> fin_cases i <;> fin_cases j <;>
    simp [pauli]

private theorem pauli_prod_conj_formula (J : Finset (Fin 20)) (a : J → Fin 4)
    (σ τ : J → Fin 2) :
    star (∏ j : J, pauli (a j) (σ j) (τ j)) =
      (-1 : ℂ) ^ pauliYCount J a * ∏ j : J, pauli (a j) (σ j) (τ j) := by
  classical
  let f : J → ℂ := fun j => pauli (a j) (σ j) (τ j)
  let y : J → Prop := fun j => a j = 2
  have hgeneral (s : Finset J) :
      star (∏ j ∈ s, f j) =
        (-1 : ℂ) ^ (s.filter y).card * ∏ j ∈ s, f j := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert j s hj ih =>
        have hfac : star (f j) = if y j then -f j else f j := by
          simp [f, y, pauli_entry_conj]
        have hjy : j ∉ s.filter y := fun hx => hj (Finset.mem_filter.mp hx).1
        by_cases hy : y j
        · have hc : ((insert j s).filter y).card = (s.filter y).card + 1 := by
            rw [Finset.filter_insert]
            simp [hy, hjy]
          rw [Finset.prod_insert hj]
          rw [star_mul, hfac, ih, hc]
          simp [hy]
          ring
        · have hc : ((insert j s).filter y).card = (s.filter y).card := by
            rw [Finset.filter_insert]
            simp [hy]
          rw [Finset.prod_insert hj]
          rw [star_mul, hfac, ih, hc]
          simp [hy]
          ring
  have h := hgeneral Finset.univ
  simpa [f, y, pauliYCount] using h

theorem main : AKLT.Blueprint.H1.PauliRealityStatement := by
  intro J p hodd σ τ
  change Complex.im (∑ a : J → Fin 4,
    (p.coeff (pauliExponent J a) : ℂ) * ∏ j : J, pauli (a j) (σ j) (τ j)) = 0
  have hterm (a : J → Fin 4) : star
      ((p.coeff (pauliExponent J a) : ℂ) * ∏ j : J, pauli (a j) (σ j) (τ j)) =
      (p.coeff (pauliExponent J a) : ℂ) * ∏ j : J, pauli (a j) (σ j) (τ j) := by
    by_cases he : Even (pauliYCount J a)
    · have hp : (-1 : ℂ) ^ pauliYCount J a = 1 := by
        rcases he with ⟨n, hn⟩
        rw [hn]
        simp
      have hprod : star (∏ j : J, pauli (a j) (σ j) (τ j)) =
          ∏ j : J, pauli (a j) (σ j) (τ j) := by
        rw [pauli_prod_conj_formula J a σ τ, hp]
        simp
      rw [star_mul, hprod]
      have hc : star (p.coeff (pauliExponent J a) : ℂ) =
          (p.coeff (pauliExponent J a) : ℂ) := by simp
      rw [hc]
      ring
    · have ho : Odd (pauliYCount J a) := Nat.not_even_iff_odd.mp he
      have hc := hodd a ho
      simp [hc]
  have hsum : star (∑ a : J → Fin 4,
      (p.coeff (pauliExponent J a) : ℂ) * ∏ j : J, pauli (a j) (σ j) (τ j)) =
      ∑ a : J → Fin 4,
        (p.coeff (pauliExponent J a) : ℂ) * ∏ j : J, pauli (a j) (σ j) (τ j) := by
    simp only [star_sum]
    exact Finset.sum_congr rfl (fun a _ => hterm a)
  have hi := congrArg Complex.im hsum
  have hi' : -Complex.im (∑ a : J → Fin 4,
        (p.coeff (pauliExponent J a) : ℂ) * ∏ j : J, pauli (a j) (σ j) (τ j)) =
      Complex.im (∑ a : J → Fin 4,
        (p.coeff (pauliExponent J a) : ℂ) * ∏ j : J, pauli (a j) (σ j) (τ j)) := by
    simpa only [RCLike.star_def, Complex.conj_im] using hi
  linarith

end AKLT.W.H1M043
