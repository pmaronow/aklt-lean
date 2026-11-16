import AKLT.Blueprint.H1.NodesSector

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.H1M036

private def splitPi {ι α : Type} [DecidableEq ι] (j : ι) :
    (ι → α) ≃ α × ({k : ι // k ≠ j} → α) where
  toFun f := (f j, fun k => f k)
  invFun p := fun k => if h : k = j then p.1 else p.2 ⟨k, h⟩
  left_inv f := by
    funext k
    by_cases h : k = j <;> simp [h]
  right_inv p := by
    rcases p with ⟨a, r⟩
    apply Prod.ext
    · simp
    · funext k
      simp [k.property]

private theorem sum_if_token_coords {J : Finset (Fin 20)} (j : J)
    (σ : J → Fin 2) (f : Fin 2 → ℂ) :
    (∑ ρ : J → Fin 2, if ∀ k, k ≠ j → σ k = ρ k then f (ρ j) else 0) = ∑ a, f a := by
  classical
  let r0 : ({k : J // k ≠ j} → Fin 2) := fun k => σ k.1
  let g : Fin 2 × ({k : J // k ≠ j} → Fin 2) → ℂ := fun p =>
    if ∀ k : J, k ≠ j → (if h : k = j then p.1 else p.2 ⟨k, h⟩) = σ k then f p.1 else 0
  have hg : ∀ ρ : J → Fin 2,
      (if ∀ k, k ≠ j → σ k = ρ k then f (ρ j) else 0) = g (splitPi j ρ) := by
    intro ρ
    congr 1
    apply propext
    constructor
    · intro h k hk
      simpa [splitPi, hk] using (h k hk).symm
    · intro h k hk
      simpa [splitPi, hk] using (h k hk).symm
  rw [Fintype.sum_equiv (splitPi j) _ g hg, Fintype.sum_prod_type]
  have hcond : ∀ a r,
      (∀ k : J, k ≠ j → (if h : k = j then a else r ⟨k, h⟩) = σ k) ↔ r = r0 := by
    intro a r
    constructor
    · intro h
      funext k
      simpa [k.property] using h k.1 k.property
    · intro h k hk
      simpa [hk, h, r0]
  simp_rw [g, hcond]
  simp [r0]

private theorem tokenMatrix_mul_same {J : Finset (Fin 20)} (j : J)
    (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    tokenMatrix J j A * tokenMatrix J j B = tokenMatrix J j (A * B) := by
  classical
  ext σ τ
  rw [Matrix.mul_apply]
  let h₁ (ρ : J → Fin 2) := ∀ k, k ≠ j → σ k = ρ k
  let h₂ (ρ : J → Fin 2) := ∀ k, k ≠ j → ρ k = τ k
  by_cases h : ∀ k, k ≠ j → σ k = τ k
  all_goals
    change (∑ ρ : J → Fin 2,
      (if h₁ ρ then A (σ j) (ρ j) else 0) * (if h₂ ρ then B (ρ j) (τ j) else 0)) =
      (if ∀ k, k ≠ j → σ k = τ k then (A * B) (σ j) (τ j) else 0)
  · have hterm (ρ : J → Fin 2) :
        (if h₁ ρ then A (σ j) (ρ j) else 0) * (if h₂ ρ then B (ρ j) (τ j) else 0) =
          if h₁ ρ then A (σ j) (ρ j) * B (ρ j) (τ j) else 0 := by
      by_cases hh : h₁ ρ
      · have hh₂ : h₂ ρ := by
          intro k hk
          exact (hh k hk).symm.trans (h k hk)
        simp [hh, hh₂]
      · simp [hh]
    calc
      (∑ ρ : J → Fin 2, (if h₁ ρ then A (σ j) (ρ j) else 0) *
          (if h₂ ρ then B (ρ j) (τ j) else 0)) =
          ∑ ρ : J → Fin 2, if h₁ ρ then A (σ j) (ρ j) * B (ρ j) (τ j) else 0 := by
            apply Finset.sum_congr rfl
            intro ρ _
            exact hterm ρ
      _ = ∑ a : Fin 2, A (σ j) a * B a (τ j) := by
            simpa [h₁] using sum_if_token_coords j σ (fun a => A (σ j) a * B a (τ j))
      _ = (if ∀ k, k ≠ j → σ k = τ k then (A * B) (σ j) (τ j) else 0) := by
            rw [Matrix.mul_apply]
            rw [if_pos h]
  · have hzero (ρ : J → Fin 2) :
        (if h₁ ρ then A (σ j) (ρ j) else 0) * (if h₂ ρ then B (ρ j) (τ j) else 0) = 0 := by
      by_cases hh₁ : h₁ ρ <;> by_cases hh₂ : h₂ ρ
      · exact (h (fun k hk => (hh₁ k hk).trans (hh₂ k hk))).elim
      · simp [hh₂]
      · simp [hh₁]
      · simp [hh₁, hh₂]
    calc
      (∑ ρ : J → Fin 2, (if h₁ ρ then A (σ j) (ρ j) else 0) *
          (if h₂ ρ then B (ρ j) (τ j) else 0)) = 0 := by
            apply Finset.sum_eq_zero
            intro ρ _
            exact hzero ρ
      _ = (if ∀ k, k ≠ j → σ k = τ k then (A * B) (σ j) (τ j) else 0) := by
            rw [if_neg h]

private theorem tokenMatrix_mul_ne_apply {J : Finset (Fin 20)} (j k : J) (hjk : j ≠ k)
    (A B : Matrix (Fin 2) (Fin 2) ℂ) (σ τ : J → Fin 2) :
    (tokenMatrix J j A * tokenMatrix J k B) σ τ =
      (if ∀ l, l ≠ j → l ≠ k → σ l = τ l then
        A (σ j) (τ j) * B (σ k) (τ k) else 0) := by
  classical
  rw [Matrix.mul_apply]
  let h₁ (ρ : J → Fin 2) := ∀ l, l ≠ j → σ l = ρ l
  let h₂ (ρ : J → Fin 2) := ∀ l, l ≠ k → ρ l = τ l
  let ρ₀ : J → Fin 2 := Function.update τ k (σ k)
  change (∑ ρ : J → Fin 2,
      (if h₁ ρ then A (σ j) (ρ j) else 0) * (if h₂ ρ then B (ρ k) (τ k) else 0)) =
    (if ∀ l, l ≠ j → l ≠ k → σ l = τ l then
      A (σ j) (τ j) * B (σ k) (τ k) else 0)
  by_cases h : ∀ l, l ≠ j → l ≠ k → σ l = τ l
  · have hρ₀₁ : h₁ ρ₀ := by
      intro l hlj
      by_cases hlk : l = k
      · subst l
        simp [ρ₀]
      · have hl := h l hlj hlk
        simpa [ρ₀, hlk] using hl
    have hρ₀₂ : h₂ ρ₀ := by
      intro l hlk
      simp [ρ₀, hlk]
    have huniq (ρ : J → Fin 2) (ha : h₁ ρ) (hb : h₂ ρ) : ρ = ρ₀ := by
      funext l
      by_cases hlk : l = k
      · subst l
        have hs := ha k (Ne.symm hjk)
        simp [ρ₀, hs]
      · have hs := hb l hlk
        simp [ρ₀, hlk, hs]
    rw [Finset.sum_eq_single ρ₀]
    · change (if h₁ ρ₀ then A (σ j) (ρ₀ j) else 0) *
        (if h₂ ρ₀ then B (ρ₀ k) (τ k) else 0) = _
      have hjval : ρ₀ j = τ j := hρ₀₂ j hjk
      have hkval : ρ₀ k = σ k := by simp [ρ₀]
      rw [if_pos hρ₀₁, if_pos hρ₀₂, if_pos h, hjval, hkval]
    · intro ρ _ hne
      by_cases ha : h₁ ρ <;> by_cases hb : h₂ ρ
      · exact (hne (huniq ρ ha hb)).elim
      · change (if h₁ ρ then A (σ j) (ρ j) else 0) *
          (if h₂ ρ then B (ρ k) (τ k) else 0) = 0
        simp [ha, hb]
      · change (if h₁ ρ then A (σ j) (ρ j) else 0) *
          (if h₂ ρ then B (ρ k) (τ k) else 0) = 0
        simp [ha, hb]
      · change (if h₁ ρ then A (σ j) (ρ j) else 0) *
          (if h₂ ρ then B (ρ k) (τ k) else 0) = 0
        simp [ha, hb]
    · simp
  · have hzero (ρ : J → Fin 2) :
        (if h₁ ρ then A (σ j) (ρ j) else 0) * (if h₂ ρ then B (ρ k) (τ k) else 0) = 0 := by
      by_cases ha : h₁ ρ <;> by_cases hb : h₂ ρ
      · exact (h (fun l hlj hlk => (ha l hlj).trans (hb l hlk))).elim
      · simp [ha, hb]
      · simp [ha, hb]
      · simp [ha, hb]
    calc
      (∑ ρ : J → Fin 2, tokenMatrix J j A σ ρ * tokenMatrix J k B ρ τ) = 0 := by
        apply Finset.sum_eq_zero
        intro ρ _
        simpa [tokenMatrix, h₁, h₂] using hzero ρ
      _ = (if ∀ l, l ≠ j → l ≠ k → σ l = τ l then
          A (σ j) (τ j) * B (σ k) (τ k) else 0) := by rw [if_neg h]

private theorem tokenMatrix_mul_ne {J : Finset (Fin 20)} (j k : J) (hjk : j ≠ k)
    (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    tokenMatrix J j A * tokenMatrix J k B = tokenMatrix J k B * tokenMatrix J j A := by
  ext σ τ
  rw [tokenMatrix_mul_ne_apply j k hjk A B, tokenMatrix_mul_ne_apply k j hjk.symm B A]
  change (if ∀ l : J, l ≠ j → l ≠ k → σ l = τ l then
      A (σ j) (τ j) * B (σ k) (τ k) else 0) =
    (if ∀ l : J, l ≠ k → l ≠ j → σ l = τ l then
      B (σ k) (τ k) * A (σ j) (τ j) else 0)
  have h₁ : (∀ l, l ≠ j → l ≠ k → σ l = τ l) →
      (∀ l, l ≠ k → l ≠ j → σ l = τ l) := by
    intro h l hlk hlj
    exact h l hlj hlk
  have h₂ : (∀ l, l ≠ k → l ≠ j → σ l = τ l) →
      (∀ l, l ≠ j → l ≠ k → σ l = τ l) := by
    intro h l hlj hlk
    exact h l hlk hlj
  by_cases h : ∀ l, l ≠ j → l ≠ k → σ l = τ l
  · rw [if_pos h, if_pos (h₁ h)]
    ring
  · have hn : ¬∀ l, l ≠ k → l ≠ j → σ l = τ l := fun hh => h (h₂ hh)
    rw [if_neg h, if_neg hn]

private theorem tokenMatrix_sub {J : Finset (Fin 20)} (j : J)
    (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    tokenMatrix J j (A - B) = tokenMatrix J j A - tokenMatrix J j B := by
  classical
  ext σ τ
  change (if ∀ k : J, k ≠ j → σ k = τ k then (A - B) (σ j) (τ j) else 0) =
    (if ∀ k : J, k ≠ j → σ k = τ k then A (σ j) (τ j) else 0) -
      (if ∀ k : J, k ≠ j → σ k = τ k then B (σ j) (τ j) else 0)
  by_cases h : ∀ k : J, k ≠ j → σ k = τ k
  · rw [if_pos h, if_pos h, if_pos h]
    simp
  · rw [if_neg h, if_neg h, if_neg h]
    simp

private theorem tokenMatrix_smul {J : Finset (Fin 20)} (j : J) (c : ℂ)
    (A : Matrix (Fin 2) (Fin 2) ℂ) :
    tokenMatrix J j (c • A) = c • tokenMatrix J j A := by
  classical
  ext σ τ
  change (if ∀ k : J, k ≠ j → σ k = τ k then (c • A) (σ j) (τ j) else 0) =
    c • (if ∀ k : J, k ≠ j → σ k = τ k then A (σ j) (τ j) else 0)
  by_cases h : ∀ k : J, k ≠ j → σ k = τ k
  · rw [if_pos h, if_pos h]
    simp
  · rw [if_neg h, if_neg h]
    simp

private theorem commutator_sum {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (A B : ι → Matrix κ κ ℂ)
    (hcross : ∀ i j, i ≠ j → A i * B j = B j * A i) :
    (∑ i, A i) * (∑ j, B j) - (∑ i, B i) * (∑ j, A j) =
      ∑ i, (A i * B i - B i * A i) := by
  classical
  have hAB : (∑ i, A i) * (∑ j, B j) = ∑ i, ∑ j, A i * B j := by
    calc
      (∑ i, A i) * (∑ j, B j) = ∑ j, ∑ i, A i * B j := by
        simp only [Finset.sum_mul, Finset.mul_sum]
      _ = ∑ i, ∑ j, A i * B j := by rw [Finset.sum_comm]
  have hBA : (∑ i, B i) * (∑ j, A j) = ∑ i, ∑ j, B j * A i := by
    calc
      (∑ i, B i) * (∑ j, A j) = ∑ j, ∑ i, B i * A j := by
        simp only [Finset.sum_mul, Finset.mul_sum]
      _ = ∑ i, ∑ j, B j * A i := by rw [Finset.sum_comm]
  calc
    (∑ i, A i) * (∑ j, B j) - (∑ i, B i) * (∑ j, A j) =
        (∑ i, ∑ j, A i * B j) - (∑ i, ∑ j, B j * A i) := by rw [hAB, hBA]
    _ = ∑ i, ∑ j, (A i * B j - B j * A i) := by
          simp_rw [← Finset.sum_sub_distrib]
    _ = ∑ i, ∑ j, if i = j then A i * B i - B i * A i else 0 := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          by_cases h : i = j
          · subst j
            simp
          · simp [h, hcross i j h]
    _ = ∑ i, (A i * B i - B i * A i) := by simp

private def localZ : Matrix (Fin 2) (Fin 2) ℂ := (1 / 2 : ℂ) • pauli 3
private def localP : Matrix (Fin 2) (Fin 2) ℂ := (1 / 2 : ℂ) • (pauli 1 + Complex.I • pauli 2)
private def localM : Matrix (Fin 2) (Fin 2) ℂ := (1 / 2 : ℂ) • (pauli 1 - Complex.I • pauli 2)

private theorem localZP : localZ * localP - localP * localZ = localP := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [localZ, localP, pauli, Matrix.mul_apply]

private theorem localZM : localZ * localM - localM * localZ = -localM := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [localZ, localM, pauli, Matrix.mul_apply]

private theorem localPM : localP * localM - localM * localP = (2 : ℂ) • localZ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [localZ, localP, localM, pauli, Matrix.mul_apply]

private theorem totalSpinZ_as_lifts (J : Finset (Fin 20)) :
    totalSpinZ J = Matrix.toEuclideanLin (∑ j : J, tokenMatrix J j localZ) := by
  change Matrix.toEuclideanLin ((1 / 2 : ℂ) • ∑ j : J, tokenMatrix J j (pauli 3)) =
    Matrix.toEuclideanLin (∑ j : J, tokenMatrix J j localZ)
  apply congrArg Matrix.toEuclideanLin
  simp_rw [localZ, tokenMatrix_smul, ← Finset.smul_sum]

private theorem totalSpinPlus_as_lifts (J : Finset (Fin 20)) :
    totalSpinPlus J = Matrix.toEuclideanLin (∑ j : J, tokenMatrix J j localP) := by
  change Matrix.toEuclideanLin ((1 / 2 : ℂ) • ∑ j : J,
      tokenMatrix J j (pauli 1 + Complex.I • pauli 2)) =
    Matrix.toEuclideanLin (∑ j : J, tokenMatrix J j localP)
  apply congrArg Matrix.toEuclideanLin
  simp_rw [localP, tokenMatrix_smul, ← Finset.smul_sum]

private theorem totalSpinMinus_as_lifts (J : Finset (Fin 20)) :
    totalSpinMinus J = Matrix.toEuclideanLin (∑ j : J, tokenMatrix J j localM) := by
  change Matrix.toEuclideanLin ((1 / 2 : ℂ) • ∑ j : J,
      tokenMatrix J j (pauli 1 - Complex.I • pauli 2)) =
    Matrix.toEuclideanLin (∑ j : J, tokenMatrix J j localM)
  apply congrArg Matrix.toEuclideanLin
  simp_rw [localM, tokenMatrix_smul, ← Finset.smul_sum]

private theorem totalZP_matrix (J : Finset (Fin 20)) :
    (∑ j : J, tokenMatrix J j localZ) * (∑ j : J, tokenMatrix J j localP) -
      (∑ j : J, tokenMatrix J j localP) * (∑ j : J, tokenMatrix J j localZ) =
        ∑ j : J, tokenMatrix J j localP := by
  calc
    _ = ∑ j : J, (tokenMatrix J j localZ * tokenMatrix J j localP -
        tokenMatrix J j localP * tokenMatrix J j localZ) := by
          apply commutator_sum
          intro j k hjk
          exact tokenMatrix_mul_ne j k hjk localZ localP
    _ = ∑ j : J, tokenMatrix J j localP := by
          apply Finset.sum_congr rfl
          intro j _
          rw [tokenMatrix_mul_same, tokenMatrix_mul_same, ← tokenMatrix_sub, localZP]

private theorem totalZM_matrix (J : Finset (Fin 20)) :
    (∑ j : J, tokenMatrix J j localZ) * (∑ j : J, tokenMatrix J j localM) -
      (∑ j : J, tokenMatrix J j localM) * (∑ j : J, tokenMatrix J j localZ) =
        -∑ j : J, tokenMatrix J j localM := by
  calc
    _ = ∑ j : J, (tokenMatrix J j localZ * tokenMatrix J j localM -
        tokenMatrix J j localM * tokenMatrix J j localZ) := by
          apply commutator_sum
          intro j k hjk
          exact tokenMatrix_mul_ne j k hjk localZ localM
    _ = -∑ j : J, tokenMatrix J j localM := by
          calc
            (∑ j : J, (tokenMatrix J j localZ * tokenMatrix J j localM -
                tokenMatrix J j localM * tokenMatrix J j localZ)) =
                ∑ j : J, -tokenMatrix J j localM := by
                  apply Finset.sum_congr rfl
                  intro j _
                  rw [tokenMatrix_mul_same, tokenMatrix_mul_same, ← tokenMatrix_sub, localZM]
                  simpa using (tokenMatrix_smul j (-1 : ℂ) localM)
            _ = -∑ j : J, tokenMatrix J j localM := by rw [Finset.sum_neg_distrib]

private theorem totalPM_matrix (J : Finset (Fin 20)) :
    (∑ j : J, tokenMatrix J j localP) * (∑ j : J, tokenMatrix J j localM) -
      (∑ j : J, tokenMatrix J j localM) * (∑ j : J, tokenMatrix J j localP) =
        (2 : ℂ) • ∑ j : J, tokenMatrix J j localZ := by
  calc
    _ = ∑ j : J, (tokenMatrix J j localP * tokenMatrix J j localM -
        tokenMatrix J j localM * tokenMatrix J j localP) := by
          apply commutator_sum
          intro j k hjk
          exact tokenMatrix_mul_ne j k hjk localP localM
    _ = ∑ j : J, (2 : ℂ) • tokenMatrix J j localZ := by
          apply Finset.sum_congr rfl
          intro j _
          rw [tokenMatrix_mul_same, tokenMatrix_mul_same, ← tokenMatrix_sub, localPM, tokenMatrix_smul]
    _ = (2 : ℂ) • ∑ j : J, tokenMatrix J j localZ := by rw [Finset.smul_sum]

theorem endZP (J : Finset (Fin 20)) :
    totalSpinZ J * totalSpinPlus J - totalSpinPlus J * totalSpinZ J = totalSpinPlus J := by
  rw [totalSpinZ_as_lifts, totalSpinPlus_as_lifts]
  change Matrix.toEuclideanLin (∑ j : J, tokenMatrix J j localZ) ∘ₗ
      Matrix.toEuclideanLin (∑ j : J, tokenMatrix J j localP) -
    Matrix.toEuclideanLin (∑ j : J, tokenMatrix J j localP) ∘ₗ
      Matrix.toEuclideanLin (∑ j : J, tokenMatrix J j localZ) =
        Matrix.toEuclideanLin (∑ j : J, tokenMatrix J j localP)
  rw [← Matrix.toLpLin_mul_same, ← Matrix.toLpLin_mul_same, ← map_sub]
  exact congrArg Matrix.toEuclideanLin (totalZP_matrix J)

theorem endZM (J : Finset (Fin 20)) :
    totalSpinZ J * totalSpinMinus J - totalSpinMinus J * totalSpinZ J = -totalSpinMinus J := by
  rw [totalSpinZ_as_lifts, totalSpinMinus_as_lifts]
  change Matrix.toEuclideanLin (∑ j : J, tokenMatrix J j localZ) ∘ₗ
      Matrix.toEuclideanLin (∑ j : J, tokenMatrix J j localM) -
    Matrix.toEuclideanLin (∑ j : J, tokenMatrix J j localM) ∘ₗ
      Matrix.toEuclideanLin (∑ j : J, tokenMatrix J j localZ) =
        -Matrix.toEuclideanLin (∑ j : J, tokenMatrix J j localM)
  rw [← Matrix.toLpLin_mul_same, ← Matrix.toLpLin_mul_same, ← map_sub, ← map_neg]
  exact congrArg Matrix.toEuclideanLin (totalZM_matrix J)

theorem endPM (J : Finset (Fin 20)) :
    totalSpinPlus J * totalSpinMinus J - totalSpinMinus J * totalSpinPlus J =
      (2 : ℂ) • totalSpinZ J := by
  rw [totalSpinPlus_as_lifts, totalSpinMinus_as_lifts, totalSpinZ_as_lifts]
  change Matrix.toEuclideanLin (∑ j : J, tokenMatrix J j localP) ∘ₗ
      Matrix.toEuclideanLin (∑ j : J, tokenMatrix J j localM) -
    Matrix.toEuclideanLin (∑ j : J, tokenMatrix J j localM) ∘ₗ
      Matrix.toEuclideanLin (∑ j : J, tokenMatrix J j localP) =
        (2 : ℂ) • Matrix.toEuclideanLin (∑ j : J, tokenMatrix J j localZ)
  rw [← Matrix.toLpLin_mul_same, ← Matrix.toLpLin_mul_same, ← map_sub, ← map_smul]
  exact congrArg Matrix.toEuclideanLin (totalPM_matrix J)

end AKLT.W.H1M036
