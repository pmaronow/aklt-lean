module
public import AKLT.Blueprint.H1.NodesStructure

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.H1M054

private def swapConfig {J : Finset (Fin 20)} (j k : J) (σ : J → Fin 2) : J → Fin 2 :=
  fun x => σ (Equiv.swap j k x)

private def swapMat (J : Finset (Fin 20)) (j k : J) : Matrix (J → Fin 2) (J → Fin 2) ℂ :=
  fun σ τ => if σ = swapConfig j k τ then 1 else 0

private theorem swapConfig_involutive {J : Finset (Fin 20)} (j k : J) (σ : J → Fin 2) :
    swapConfig j k (swapConfig j k σ) = σ := by
  funext x
  simp [swapConfig]

private theorem swap_left_token (J : Finset (Fin 20)) (j k : J)
    (A : Matrix (Fin 2) (Fin 2) ℂ) :
    swapMat J j k * tokenMatrix J j A = tokenMatrix J k A * swapMat J j k := by
  ext σ τ
  rw [Matrix.mul_apply, Matrix.mul_apply]
  have huniq (ρ : J → Fin 2) : σ = swapConfig j k ρ ↔ ρ = swapConfig j k σ := by
    constructor
    · intro h
      calc
        ρ = swapConfig j k (swapConfig j k ρ) := (swapConfig_involutive j k ρ).symm
        _ = swapConfig j k σ := by rw [h]
    · intro h
      rw [h, swapConfig_involutive]
  have hcond : (∀ x : J, x ≠ j → σ (Equiv.swap j k x) = τ x) ↔
      (∀ x : J, x ≠ k → σ x = τ (Equiv.swap j k x)) := by
    constructor
    · intro h x hx
      have hne : Equiv.swap j k x ≠ j := by
        intro heq
        apply hx
        have hh := congrArg (Equiv.swap j k) heq
        simpa using hh
      have hh := h (Equiv.swap j k x) hne
      simpa using hh
    · intro h x hx
      have hne : Equiv.swap j k x ≠ k := by
        intro heq
        apply hx
        have hh := congrArg (Equiv.swap j k) heq
        simpa using hh
      have hh := h (Equiv.swap j k x) hne
      simpa using hh
  have hleft : (∑ ρ : J → Fin 2, swapMat J j k σ ρ * tokenMatrix J j A ρ τ) =
      tokenMatrix J j A (swapConfig j k σ) τ := by
    rw [Finset.sum_eq_single (swapConfig j k σ)]
    · simp [swapMat, huniq]
    · intro ρ _ hρ
      simp [swapMat, huniq, hρ]
    · simp
  have hright : (∑ ρ : J → Fin 2, tokenMatrix J k A σ ρ * swapMat J j k ρ τ) =
      tokenMatrix J k A σ (swapConfig j k τ) := by
    rw [Finset.sum_eq_single (swapConfig j k τ)]
    · simp [swapMat]
    · intro ρ _ hρ
      simp [swapMat, hρ]
    · simp
  rw [hleft, hright]
  change (if ∀ x : J, x ≠ j → σ (Equiv.swap j k x) = τ x then
        A ((swapConfig j k σ) j) (τ j) else 0) =
      (if ∀ x : J, x ≠ k → σ x = (swapConfig j k τ) x then
        A (σ k) ((swapConfig j k τ) k) else 0)
  have hcond' : (∀ a : Fin 20, ∀ b : a ∈ J, ¬ (⟨a, b⟩ : J) = j →
        σ (Equiv.swap j k ⟨a, b⟩) = τ ⟨a, b⟩) ↔
      (∀ a : Fin 20, ∀ b : a ∈ J, ¬ (⟨a, b⟩ : J) = k →
        σ ⟨a, b⟩ = τ (Equiv.swap j k ⟨a, b⟩)) := by
    simpa using hcond
  simp [hcond', swapConfig, Equiv.swap_apply_left, Equiv.swap_apply_right]

private theorem token_commute (J : Finset (Fin 20)) (j k : J)
    (A : Matrix (Fin 2) (Fin 2) ℂ) :
    tokenMatrix J j A * tokenMatrix J k A = tokenMatrix J k A * tokenMatrix J j A := by
  by_cases hjk : j = k
  · subst k
    rfl
  · classical
    ext σ τ
    rw [Matrix.mul_apply, Matrix.mul_apply]
    let ρ₁ : J → Fin 2 := fun x => if x = j then τ j else σ x
    let ρ₂ : J → Fin 2 := fun x => if x = k then τ k else σ x
    let H : Prop := ∀ x : J, x ≠ j → x ≠ k → σ x = τ x
    have hzero₁ (ρ : J → Fin 2) (hρ : ρ ≠ ρ₁) :
        tokenMatrix J j A σ ρ * tokenMatrix J k A ρ τ = 0 := by
      change (if ∀ x : J, x ≠ j → σ x = ρ x then A (σ j) (ρ j) else 0) *
        (if ∀ x : J, x ≠ k → ρ x = τ x then A (ρ k) (τ k) else 0) = 0
      by_cases h₁ : ∀ x : J, x ≠ j → σ x = ρ x
      · by_cases h₂ : ∀ x : J, x ≠ k → ρ x = τ x
        · have heq : ρ = ρ₁ := by
            funext x
            by_cases hx : x = j
            · subst x
              have h := h₂ j hjk
              simpa [ρ₁] using h
            · have h := h₁ x hx
              calc
                ρ x = σ x := h.symm
                _ = ρ₁ x := by simp [ρ₁, hx]
          exact (hρ heq).elim
        · rw [if_pos h₁, if_neg h₂]
          simp
      · rw [if_neg h₁]
        simp
    have hzero₂ (ρ : J → Fin 2) (hρ : ρ ≠ ρ₂) :
        tokenMatrix J k A σ ρ * tokenMatrix J j A ρ τ = 0 := by
      change (if ∀ x : J, x ≠ k → σ x = ρ x then A (σ k) (ρ k) else 0) *
        (if ∀ x : J, x ≠ j → ρ x = τ x then A (ρ j) (τ j) else 0) = 0
      by_cases h₁ : ∀ x : J, x ≠ k → σ x = ρ x
      · by_cases h₂ : ∀ x : J, x ≠ j → ρ x = τ x
        · have heq : ρ = ρ₂ := by
            funext x
            by_cases hx : x = k
            · subst x
              have h := h₂ k (Ne.symm hjk)
              simpa [ρ₂] using h
            · have h := h₁ x hx
              calc
                ρ x = σ x := h.symm
                _ = ρ₂ x := by simp [ρ₂, hx]
          exact (hρ heq).elim
        · rw [if_pos h₁, if_neg h₂]
          simp
      · rw [if_neg h₁]
        simp
    have hleft : (∑ ρ : J → Fin 2, tokenMatrix J j A σ ρ * tokenMatrix J k A ρ τ) =
        if H then A (σ j) (τ j) * A (σ k) (τ k) else 0 := by
      rw [Finset.sum_eq_single ρ₁]
      · have hfirst : (∀ x : J, x ≠ j → σ x = ρ₁ x) := by
          intro x hx
          simp [ρ₁, hx]
        have hsecond : (∀ x : J, x ≠ k → ρ₁ x = τ x) ↔ H := by
          constructor
          · intro h x hxj hxk
            have hh := h x hxk
            simpa [ρ₁, hxj] using hh
          · intro h x hxk
            by_cases hxj : x = j
            · subst x
              simp [ρ₁]
            · have hh := h x hxj hxk
              simpa [ρ₁, hxj] using hh
        change (if ∀ x : J, x ≠ j → σ x = ρ₁ x then A (σ j) (ρ₁ j) else 0) *
          (if ∀ x : J, x ≠ k → ρ₁ x = τ x then A (ρ₁ k) (τ k) else 0) = _
        rw [if_pos hfirst]
        by_cases hH : H
        · have hsec := hsecond.mpr hH
          rw [if_pos hsec, if_pos hH]
          simp [ρ₁, Ne.symm hjk]
        · have hsec : ¬ (∀ x : J, x ≠ k → ρ₁ x = τ x) := fun hh => hH (hsecond.mp hh)
          rw [if_neg hsec, if_neg hH]
          simp [ρ₁, hjk]
      · intro ρ _ hρ
        exact hzero₁ ρ hρ
      · simp
    have hright : (∑ ρ : J → Fin 2, tokenMatrix J k A σ ρ * tokenMatrix J j A ρ τ) =
        if H then A (σ k) (τ k) * A (σ j) (τ j) else 0 := by
      rw [Finset.sum_eq_single ρ₂]
      · have hfirst : (∀ x : J, x ≠ k → σ x = ρ₂ x) := by
          intro x hx
          simp [ρ₂, hx]
        have hsecond : (∀ x : J, x ≠ j → ρ₂ x = τ x) ↔ H := by
          constructor
          · intro h x hxj hxk
            have hh := h x hxj
            simpa [ρ₂, hxk] using hh
          · intro h x hxj
            by_cases hxk : x = k
            · subst x
              simp [ρ₂]
            · have hh := h x hxj hxk
              simpa [ρ₂, hxk] using hh
        change (if ∀ x : J, x ≠ k → σ x = ρ₂ x then A (σ k) (ρ₂ k) else 0) *
          (if ∀ x : J, x ≠ j → ρ₂ x = τ x then A (ρ₂ j) (τ j) else 0) = _
        rw [if_pos hfirst]
        by_cases hH : H
        · have hsec := hsecond.mpr hH
          rw [if_pos hsec, if_pos hH]
          simp [ρ₂, hjk]
        · have hsec : ¬ (∀ x : J, x ≠ j → ρ₂ x = τ x) := fun hh => hH (hsecond.mp hh)
          rw [if_neg hsec, if_neg hH]
          simp [ρ₂, hjk]
      · intro ρ _ hρ
        exact hzero₂ ρ hρ
      · simp
    rw [hleft, hright]
    by_cases hH : H <;> simp [hH, mul_comm]

private theorem swapMat_comm (J : Finset (Fin 20)) (j k : J) :
    swapMat J j k = swapMat J k j := by
  ext σ τ
  have hswap : swapConfig j k τ = swapConfig k j τ := by
    funext x
    exact congrArg (fun e : Equiv.Perm J => τ (e x)) (Equiv.swap_comm j k)
  change (if σ = swapConfig j k τ then (1 : ℂ) else 0) =
    if σ = swapConfig k j τ then 1 else 0
  rw [hswap]

private theorem pairMatrix_commute (J : Finset (Fin 20)) (j k : J)
    (A : Matrix (Fin 2) (Fin 2) ℂ) :
    Commute (tokenMatrix J j A * tokenMatrix J k A) (swapMat J j k) := by
  let Tj := tokenMatrix J j A
  let Tk := tokenMatrix J k A
  let P := swapMat J j k
  have hPj : P * Tj = Tk * P := by
    exact swap_left_token J j k A
  have hPk' : swapMat J k j * tokenMatrix J k A = tokenMatrix J j A * swapMat J k j :=
    swap_left_token J k j A
  have hPk : P * Tk = Tj * P := by
    simpa [P, swapMat_comm] using hPk'
  change (Tj * Tk) * P = P * (Tj * Tk)
  calc
    (Tj * Tk) * P = Tj * (Tk * P) := by rw [mul_assoc]
    _ = Tj * (P * Tj) := by rw [← hPj]
    _ = (Tj * P) * Tj := by rw [mul_assoc]
    _ = (P * Tk) * Tj := by rw [← hPk]
    _ = P * (Tk * Tj) := by rw [mul_assoc]
    _ = P * (Tj * Tk) := by rw [← token_commute J j k A]

private theorem matrix_commute_toEuclideanLin {ι : Type} [Fintype ι] [DecidableEq ι]
    (X Y : Matrix ι ι ℂ) (h : X * Y = Y * X) :
    Commute (Matrix.toEuclideanLin X) (Matrix.toEuclideanLin Y) := by
  change (Matrix.toEuclideanLin X) ∘ₗ (Matrix.toEuclideanLin Y) =
    (Matrix.toEuclideanLin Y) ∘ₗ (Matrix.toEuclideanLin X)
  have h' := congrArg (Matrix.toEuclideanLin) h
  simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same] using h'

theorem main : AKLT.Blueprint.H1.EqualPairExchangeStatement := by
  intro J j k η n
  let A : Matrix (Fin 2) (Fin 2) ℂ := 1 + (η : ℂ) • AKLT.Blueprint.H1.blochMatrix n
  have hmat : Commute (tokenMatrix J j A * tokenMatrix J k A) (swapMat J j k) :=
    pairMatrix_commute J j k A
  change tokenMatrix J j A * tokenMatrix J k A * swapMat J j k =
    swapMat J j k * (tokenMatrix J j A * tokenMatrix J k A) at hmat
  have hop := matrix_commute_toEuclideanLin (tokenMatrix J j A * tokenMatrix J k A)
    (swapMat J j k) hmat
  change Commute
    (Matrix.toEuclideanLin (tokenMatrix J j (1 + (η : ℂ) • AKLT.Blueprint.H1.blochMatrix n) *
      tokenMatrix J k (1 + (η : ℂ) • AKLT.Blueprint.H1.blochMatrix n)))
    (Matrix.toEuclideanLin (swapMat J j k))
  simpa [A, AKLT.Blueprint.H1.pairTerm, AKLT.Defs.exchangeOperator, swapMat] using hop

#print axioms main

end AKLT.W.H1M054
