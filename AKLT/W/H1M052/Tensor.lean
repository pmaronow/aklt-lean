import AKLT.Blueprint.H1.NodesStructure

noncomputable section
open scoped BigOperators ComplexOrder
open AKLT.Defs AKLT.Blueprint.H1

namespace AKLT.W.H1M052

abbrev SmallMatrix := Matrix (Fin 2) (Fin 2) ℂ

def tensorMatrix (J : Finset (Fin 20)) (A : J → SmallMatrix) :
    Matrix (J → Fin 2) (J → Fin 2) ℂ := fun σ τ => ∏ j, A j (σ j) (τ j)

@[simp] theorem tensorMatrix_one (J : Finset (Fin 20)) :
    tensorMatrix J (fun _ => 1) = 1 := by
  classical
  ext σ τ
  simp only [tensorMatrix, Matrix.one_apply]
  by_cases h : σ = τ
  · subst τ; simp
  · rw [ite_eq_right h]
    obtain ⟨j, hj⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ j) (ite_eq_right hj)

theorem tensorMatrix_mul (J : Finset (Fin 20)) (A B : J → SmallMatrix) :
    tensorMatrix J (fun j => A j * B j) = tensorMatrix J A * tensorMatrix J B := by
  classical
  ext σ τ
  simp only [tensorMatrix, Matrix.mul_apply, ← Finset.prod_mul_distrib]
  exact Fintype.prod_sum (fun j b => A j (σ j) b * B j b (τ j))

theorem tensorMatrix_single (J : Finset (Fin 20)) (j : J) (A : SmallMatrix) :
    tensorMatrix J (fun l => if l = j then A else 1) = tokenMatrix J j A := by
  classical
  ext σ τ
  rw [tensorMatrix, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
  simp only [ite_true]
  by_cases h : ∀ k, k ≠ j → σ k = τ k
  · rw [tokenMatrix, ite_eq_left h]
    have hp : ∏ l ∈ (Finset.univ : Finset J).erase j,
        (if l = j then A else 1) (σ l) (τ l) = (1 : ℂ) := by
      apply Finset.prod_eq_one
      intro l hl
      simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hl
      simp [hl, Matrix.one_apply, h l hl]
    rw [hp, mul_one]
  · rw [tokenMatrix, ite_eq_right h]
    obtain ⟨l, hlj, hl⟩ : ∃ l, l ≠ j ∧ σ l ≠ τ l := by simpa using h
    have hp : ∏ l ∈ (Finset.univ : Finset J).erase j,
        (if l = j then A else 1) (σ l) (τ l) = (0 : ℂ) := by
      apply Finset.prod_eq_zero (i := l) (by simp [hlj])
      simp [hlj, hl]
    rw [hp, mul_zero]

abbrev toEnd {J : Finset (Fin 20)}
    (M : Matrix (J → Fin 2) (J → Fin 2) ℂ) := Matrix.toEuclideanLin M

@[simp] theorem toEnd_mul {J : Finset (Fin 20)}
    (A B : Matrix (J → Fin 2) (J → Fin 2) ℂ) :
    toEnd (A * B) = toEnd A * toEnd B := by
  exact Matrix.toLpLin_mul 2 2 2 A B

@[simp] theorem toEnd_one (J : Finset (Fin 20)) :
    toEnd (1 : Matrix (J → Fin 2) (J → Fin 2) ℂ) = 1 := by
  exact Matrix.toLpLin_one 2

def swapMatrix {J : Finset (Fin 20)} (j k : J) :
    Matrix (J → Fin 2) (J → Fin 2) ℂ :=
  fun σ τ => if σ = τ ∘ Equiv.swap j k then 1 else 0

theorem mul_swapMatrix {J : Finset (Fin 20)} (j k : J)
    (A : Matrix (J → Fin 2) (J → Fin 2) ℂ) (σ τ : J → Fin 2) :
    (A * swapMatrix j k) σ τ = A σ (τ ∘ Equiv.swap j k) := by
  classical
  simp [Matrix.mul_apply, swapMatrix]

theorem swapMatrix_mul {J : Finset (Fin 20)} (j k : J)
    (A : Matrix (J → Fin 2) (J → Fin 2) ℂ) (σ τ : J → Fin 2) :
    (swapMatrix j k * A) σ τ = A (σ ∘ Equiv.swap j k) τ := by
  classical
  have hs (a : J → Fin 2) : σ = a ∘ Equiv.swap j k ↔ a = σ ∘ Equiv.swap j k := by
    constructor
    · intro h
      funext l
      have := congrFun h (Equiv.swap j k l)
      simpa using this.symm
    · intro h
      subst a
      ext l
      simp
  simp [Matrix.mul_apply, swapMatrix, hs]

theorem tensorMatrix_commute_swap {J : Finset (Fin 20)} (j k : J)
    (A : J → SmallMatrix) (h : A j = A k) :
    Commute (tensorMatrix J A) (swapMatrix j k) := by
  classical
  change _ = _
  ext σ τ
  rw [mul_swapMatrix, swapMatrix_mul]
  simp only [tensorMatrix, Function.comp_apply]
  calc
    _ = ∏ l : J, A (Equiv.swap j k l) (σ (Equiv.swap j k l))
        (τ (Equiv.swap j k (Equiv.swap j k l))) :=
      (Fintype.prod_equiv (Equiv.swap j k) _ _ (fun l => rfl)).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro l _
      have he : A (Equiv.swap j k l) = A l := by
        by_cases hl : l = j
        · subst l; simpa using h.symm
        · by_cases hk : l = k
          · subst l; simpa using h
          · simp [Equiv.swap_apply_of_ne_of_ne hl hk]
      simp [he]

theorem tensorEnd_commute_pair {J : Finset (Fin 20)} (j k : J)
    (A : J → SmallMatrix) (h : A j = A k) :
    Commute (toEnd (tensorMatrix J A)) (exchangeOperator J j k) ∧
      Commute (toEnd (tensorMatrix J A)) (symmetricPairProjection J j k) := by
  have hc : Commute (toEnd (tensorMatrix J A)) (exchangeOperator J j k) := by
    have hm := congrArg (fun M => toEnd M) (tensorMatrix_commute_swap j k A h).eq
    have he : toEnd (swapMatrix (J := J) j k) = exchangeOperator J j k := by
      apply congrArg Matrix.toEuclideanLin
      ext σ τ
      simp only [swapMatrix, Function.comp_def]
    simp only [toEnd_mul, he] at hm
    exact hm
  refine ⟨hc, ?_⟩
  exact (Commute.one_right _ |>.add_right hc).smul_right (1 / 2 : ℂ)

/-- The remaining tensor has identity in each of the chosen pair's slots. -/
def remainingTensor {J : Finset (Fin 20)} (j k : J) (A : J → SmallMatrix) :
    Matrix (J → Fin 2) (J → Fin 2) ℂ :=
  tensorMatrix J (fun l => if l = j ∨ l = k then 1 else A l)

theorem remainingTensor_commute {J : Finset (Fin 20)} (j k : J) (A : J → SmallMatrix) :
    Commute (toEnd (remainingTensor j k A)) (exchangeOperator J j k) ∧
      Commute (toEnd (remainingTensor j k A)) (symmetricPairProjection J j k) := by
  classical
  apply tensorEnd_commute_pair
  simp

theorem tensorMatrix_factor_pair {J : Finset (Fin 20)} (j k : J) (hjk : j ≠ k)
    (A : J → SmallMatrix) (B : SmallMatrix) (hj : A j = B) (hk : A k = B) :
    tensorMatrix J A = (tokenMatrix J j B * tokenMatrix J k B) * remainingTensor j k A := by
  classical
  rw [← tensorMatrix_single, ← tensorMatrix_single, ← tensorMatrix_mul,
    remainingTensor, ← tensorMatrix_mul]
  congr 1
  funext l
  by_cases hlj : l = j
  · subst l; simp [hjk, hj]
  · by_cases hlk : l = k
    · subst l; simp [hjk.symm, hk]
    · simp [hlj, hlk]

end AKLT.W.H1M052
