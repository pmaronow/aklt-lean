import AKLT.Blueprint.H1.NodesStructure

noncomputable section
open scoped BigOperators
open AKLT.Defs
open AKLT.Blueprint.H1

namespace AKLT.W.H1M047

lemma tensorPower_conjTranspose (J : Finset (Fin 20))
    (g : Matrix (Fin 2) (Fin 2) ℂ) :
    (tensorPowerMatrix J g).conjTranspose = tensorPowerMatrix J g.conjTranspose := by
  ext σ τ
  simp [tensorPowerMatrix, Matrix.conjTranspose_apply]

lemma tensorPower_left_unitary (J : Finset (Fin 20))
    (g : Matrix (Fin 2) (Fin 2) ℂ)
    (hg : g.conjTranspose * g = 1) :
    (tensorPowerMatrix J g).conjTranspose * tensorPowerMatrix J g = 1 := by
  rw [tensorPower_conjTranspose]
  ext σ τ
  simp only [Matrix.mul_apply, tensorPowerMatrix]
  have hprod (f k : J → ℂ) :
      (∏ j : J, f j) * ∏ j : J, k j = ∏ j : J, f j * k j := by
    simpa using (Finset.prod_mul_distrib (s := Finset.univ) (f := f) (g := k)).symm
  simp_rw [hprod]
  rw [← Fintype.prod_sum (f := fun j t =>
    g.conjTranspose (σ j) t * g t (τ j))]
  have hEntry (x y : Fin 2) :
      (∑ z : Fin 2, g.conjTranspose x z * g z y) = if x = y then 1 else 0 := by
    rw [← Matrix.mul_apply, hg]
    simp [Matrix.one_apply]
  simp_rw [hEntry]
  by_cases hστ : σ = τ
  · subst τ
    simp
  · obtain ⟨j, hj⟩ : ∃ j : J, σ j ≠ τ j := by
      by_contra h
      push Not at h
      exact hστ (funext h)
    have hzero : (∏ j : J, if σ j = τ j then (1 : ℂ) else 0) = 0 := by
      apply Finset.prod_eq_zero (s := Finset.univ) (Finset.mem_univ j)
      simp [hj]
    simpa [Finset.prod_attach, Matrix.one_apply, hστ] using hzero

lemma tensorPower_right_unitary (J : Finset (Fin 20))
    (g : Matrix (Fin 2) (Fin 2) ℂ)
    (hg : g.conjTranspose * g = 1) :
    tensorPowerMatrix J g * (tensorPowerMatrix J g).conjTranspose = 1 := by
  have hgg : g * g.conjTranspose = 1 :=
    (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl (Fin 2))).mp hg
  have h := tensorPower_left_unitary J g.conjTranspose (by simpa using hgg)
  simpa [tensorPower_conjTranspose] using h

/-- The coefficient of output Pauli `b` from input Pauli `a` under the supplied
adjoint rotation. Index zero denotes the identity matrix. -/
def pauliRotationCoefficient (R : Matrix (Fin 3) (Fin 3) ℝ)
    (b a : Fin 4) : ℝ :=
  if ha : a = 0 then if b = 0 then 1 else 0 else
    if hb : b = 0 then 0 else
      R ⟨b.val - 1, by omega⟩ ⟨a.val - 1, by omega⟩

def rotatedPauliCoefficient (J : Finset (Fin 20)) (p : VectorPolynomial)
    (R : Matrix (Fin 3) (Fin 3) ℝ) (b : J → Fin 4) : ℂ :=
  ∑ a : J → Fin 4, (p.coeff (pauliExponent J a) : ℂ) *
    ∏ j : J, (pauliRotationCoefficient R (b j) (a j) : ℂ)

def rotatedPauliOperator (J : Finset (Fin 20)) (p : VectorPolynomial)
    (R : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (J → Fin 2) (J → Fin 2) ℂ :=
  fun σ τ => ∑ b : J → Fin 4, rotatedPauliCoefficient J p R b *
    ∏ j : J, pauli (b j) (σ j) (τ j)


end AKLT.W.H1M047
