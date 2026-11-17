module
public import AKLT.Blueprint.H1.NodesStructure

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators ComplexOrder
open AKLT.Defs AKLT.Blueprint.H1

namespace AKLT.W.H1M053

private lemma token_mul_apply {J : Finset (Fin 20)} (j k : J) (hjk : j ≠ k)
    (A B : Matrix (Fin 2) (Fin 2) ℂ) (σ τ : J → Fin 2) :
    (tokenMatrix J j A * tokenMatrix J k B) σ τ =
      if ∀ l : J, l ≠ j → l ≠ k → σ l = τ l then
        A (σ j) (τ j) * B (σ k) (τ k) else 0 := by
  classical
  let μ₀ : J → Fin 2 := Function.update τ k (σ k)
  have hμj : μ₀ j = τ j := by simp [μ₀, hjk]
  have hμk : μ₀ k = σ k := by simp [μ₀]
  have hc1 : (∀ l : J, l ≠ j → σ l = μ₀ l) ↔
      ∀ l : J, l ≠ j → l ≠ k → σ l = τ l := by
    constructor
    · intro h l hlj hlk
      simpa [μ₀, hlk] using h l hlj
    · intro h l hlj
      by_cases hlk : l = k
      · subst l
        simp [μ₀]
      · simpa [μ₀, hlk] using h l hlj hlk
  have hc2 : ∀ l : J, l ≠ k → μ₀ l = τ l := by
    intro l hlk
    simp [μ₀, hlk]
  rw [Matrix.mul_apply, Fintype.sum_eq_single μ₀]
  · change (if ∀ l : J, l ≠ j → σ l = μ₀ l then A (σ j) (μ₀ j) else 0) *
      (if ∀ l : J, l ≠ k → μ₀ l = τ l then B (μ₀ k) (τ k) else 0) =
      (if ∀ l : J, l ≠ j → l ≠ k → σ l = τ l then
        A (σ j) (τ j) * B (σ k) (τ k) else 0)
    by_cases hrest : ∀ l : J, l ≠ j → l ≠ k → σ l = τ l
    · have hp1 := hc1.mpr hrest
      have hp2 := hc2
      rw [if_pos hp1, if_pos hp2, if_pos hrest, hμj, hμk]
    · have hn1 : ¬ (∀ l : J, l ≠ j → σ l = μ₀ l) := fun hh => hrest (hc1.mp hh)
      have hp2 := hc2
      rw [if_neg hn1, if_pos hp2, if_neg hrest]
      simp
  · intro μ hμ
    change (if ∀ l : J, l ≠ j → σ l = μ l then A (σ j) (μ j) else 0) *
      (if ∀ l : J, l ≠ k → μ l = τ l then B (μ k) (τ k) else 0) = 0
    by_cases h₁ : ∀ l : J, l ≠ j → σ l = μ l
    · by_cases h₂ : ∀ l : J, l ≠ k → μ l = τ l
      · have heq : μ = μ₀ := by
          funext l
          by_cases hlk : l = k
          · subst l
            have hh := h₁ k (Ne.symm hjk)
            simpa [μ₀] using hh.symm
          · have hh := h₂ l hlk
            simpa [μ₀, hlk] using hh
        exact (hμ heq).elim
      · rw [if_pos h₁, if_neg h₂]
        simp
    · rw [if_neg h₁]
      simp

private lemma factor_det (η : ℝ) (n : Vec3) (hη : η ^ 2 = 1) (hn : normSq n = 1) :
    (1 + (η : ℂ) • blochMatrix n).det = 0 := by
  have hnorm : n 0 * n 0 + n 1 * n 1 + n 2 * n 2 = 1 := by
    simpa [normSq, dot, Fin.sum_univ_succ, add_assoc] using hn
  rw [Matrix.det_fin_two]
  simp [blochMatrix, pauli, Matrix.one_apply, Matrix.smul_apply, Matrix.add_apply,
    Fin.sum_univ_succ, hη]
  -- arithmetic in the three real coordinates
  have hηC : (η : ℂ) ^ 2 = 1 := by exact_mod_cast hη
  have hnC : (n 0 : ℂ) ^ 2 + (n 1 : ℂ) ^ 2 + (n 2 : ℂ) ^ 2 = 1 := by
    exact_mod_cast (by simpa [pow_two] using hnorm)
  push_cast
  ring_nf
  rw [Complex.I_sq, hηC]
  linear_combination -hnC

private lemma det_zero_minor (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.det = 0)
    (a b c d : Fin 2) : A b c * A a d = A a c * A b d := by
  have hdet : A 0 0 * A 1 1 = A 0 1 * A 1 0 := by
    rw [Matrix.det_fin_two] at hA
    exact sub_eq_zero.mp hA
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp_all [hdet, mul_comm]

private def swapIndex {J : Finset (Fin 20)} (j k : J) (σ : J → Fin 2) : J → Fin 2 :=
  fun l => σ (Equiv.swap j k l)

private lemma token_pair_row_swap {J : Finset (Fin 20)} (j k : J) (hjk : j ≠ k)
    (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.det = 0) (σ τ : J → Fin 2) :
    (tokenMatrix J j A * tokenMatrix J k A) (swapIndex j k σ) τ =
      (tokenMatrix J j A * tokenMatrix J k A) σ τ := by
  rw [token_mul_apply j k hjk A A (swapIndex j k σ) τ,
    token_mul_apply j k hjk A A σ τ]
  change (if ∀ l : J, l ≠ j → l ≠ k → swapIndex j k σ l = τ l then
      A (swapIndex j k σ j) (τ j) * A (swapIndex j k σ k) (τ k) else 0) =
    (if ∀ l : J, l ≠ j → l ≠ k → σ l = τ l then
      A (σ j) (τ j) * A (σ k) (τ k) else 0)
  have hcond : (∀ l : J, l ≠ j → l ≠ k → swapIndex j k σ l = τ l) ↔
      ∀ l : J, l ≠ j → l ≠ k → σ l = τ l := by
    constructor <;> intro hh l hlj hlk
    · simpa [swapIndex, Equiv.swap_apply_of_ne_of_ne hlj hlk] using hh l hlj hlk
    · simpa [swapIndex, Equiv.swap_apply_of_ne_of_ne hlj hlk] using hh l hlj hlk
  have hm := det_zero_minor A hA (σ j) (σ k) (τ j) (τ k)
  by_cases hl : ∀ l : J, l ≠ j → l ≠ k → swapIndex j k σ l = τ l
  · by_cases hr : ∀ l : J, l ≠ j → l ≠ k → σ l = τ l
    · rw [if_pos hl, if_pos hr]
      simpa [swapIndex, Equiv.swap_apply_left, Equiv.swap_apply_right] using hm
    · rw [if_pos hl, if_neg hr]
      exact False.elim (hr (hcond.mp hl))
  · by_cases hr : ∀ l : J, l ≠ j → l ≠ k → σ l = τ l
    · rw [if_neg hl, if_pos hr]
      exact False.elim (hl (hcond.mpr hr))
    · rw [if_neg hl, if_neg hr]

private lemma token_pair_col_swap {J : Finset (Fin 20)} (j k : J) (hjk : j ≠ k)
    (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.det = 0) (σ τ : J → Fin 2) :
    (tokenMatrix J j A * tokenMatrix J k A) σ (swapIndex j k τ) =
      (tokenMatrix J j A * tokenMatrix J k A) σ τ := by
  rw [token_mul_apply j k hjk A A σ (swapIndex j k τ),
    token_mul_apply j k hjk A A σ τ]
  change (if ∀ l : J, l ≠ j → l ≠ k → σ l = swapIndex j k τ l then
      A (σ j) (swapIndex j k τ j) * A (σ k) (swapIndex j k τ k) else 0) =
    (if ∀ l : J, l ≠ j → l ≠ k → σ l = τ l then
      A (σ j) (τ j) * A (σ k) (τ k) else 0)
  have hcond : (∀ l : J, l ≠ j → l ≠ k → σ l = swapIndex j k τ l) ↔
      ∀ l : J, l ≠ j → l ≠ k → σ l = τ l := by
    constructor <;> intro hh l hlj hlk
    · simpa [swapIndex, Equiv.swap_apply_of_ne_of_ne hlj hlk] using hh l hlj hlk
    · simpa [swapIndex, Equiv.swap_apply_of_ne_of_ne hlj hlk] using hh l hlj hlk
  have hm := det_zero_minor A hA (σ j) (σ k) (τ j) (τ k)
  by_cases hl : ∀ l : J, l ≠ j → l ≠ k → σ l = swapIndex j k τ l
  · by_cases hr : ∀ l : J, l ≠ j → l ≠ k → σ l = τ l
    · rw [if_pos hl, if_pos hr]
      have hj : swapIndex j k τ j = τ k := by simp [swapIndex, Equiv.swap_apply_left]
      have hk : swapIndex j k τ k = τ j := by simp [swapIndex, Equiv.swap_apply_right]
      rw [hj, hk]
      simpa [mul_comm] using hm
    · rw [if_pos hl, if_neg hr]
      exact False.elim (hr (hcond.mp hl))
  · by_cases hr : ∀ l : J, l ≠ j → l ≠ k → σ l = τ l
    · rw [if_neg hl, if_pos hr]
      exact False.elim (hl (hcond.mpr hr))
    · rw [if_neg hl, if_neg hr]

private def exchangeMatrix {J : Finset (Fin 20)} (j k : J) : Matrix (J → Fin 2) (J → Fin 2) ℂ :=
  fun σ τ => if σ = swapIndex j k τ then 1 else 0

private lemma exchangeMatrix_mul_apply {J : Finset (Fin 20)} (j k : J)
    (M : Matrix (J → Fin 2) (J → Fin 2) ℂ) (σ τ : J → Fin 2) :
    (exchangeMatrix j k * M) σ τ = M (swapIndex j k σ) τ := by
  classical
  let ρ₀ := swapIndex j k σ
  have hρ₀ : σ = swapIndex j k ρ₀ := by
    funext l
    simp [ρ₀, swapIndex]
  rw [Matrix.mul_apply, Fintype.sum_eq_single ρ₀]
  · change (if σ = swapIndex j k ρ₀ then 1 else 0) * M ρ₀ τ = M (swapIndex j k σ) τ
    rw [if_pos hρ₀]
    simp only [one_mul]
    rfl
  · intro ρ hρ
    by_cases heq : σ = swapIndex j k ρ
    · have huniq : ρ = ρ₀ := by
        funext l
        have hh := congrFun heq (Equiv.swap j k l)
        have hh' : σ (Equiv.swap j k l) = ρ l := by
          simpa [swapIndex] using hh
        exact hh'.symm
      exact (hρ huniq).elim
    · simp [exchangeMatrix, heq]

private lemma mul_exchangeMatrix_apply {J : Finset (Fin 20)} (j k : J)
    (M : Matrix (J → Fin 2) (J → Fin 2) ℂ) (σ τ : J → Fin 2) :
    (M * exchangeMatrix j k) σ τ = M σ (swapIndex j k τ) := by
  classical
  let ρ₀ := swapIndex j k τ
  rw [Matrix.mul_apply, Fintype.sum_eq_single ρ₀]
  · simp [exchangeMatrix, ρ₀]
  · intro ρ hρ
    simp [exchangeMatrix, ρ₀, hρ]

theorem main : AKLT.Blueprint.H1.UnitPairSupportStatement := by
  intro J j k hjk η hη n hn
  let A : Matrix (Fin 2) (Fin 2) ℂ := 1 + (η : ℂ) • blochMatrix n
  let P : Matrix (J → Fin 2) (J → Fin 2) ℂ :=
    tokenMatrix J j A * tokenMatrix J k A
  have hA : A.det = 0 := by
    exact factor_det η n hη hn
  have hleftM : exchangeMatrix j k * P = P := by
    ext σ τ
    rw [exchangeMatrix_mul_apply]
    exact token_pair_row_swap j k hjk A hA σ τ
  have hrightM : P * exchangeMatrix j k = P := by
    ext σ τ
    rw [mul_exchangeMatrix_apply]
    exact token_pair_col_swap j k hjk A hA σ τ
  have hleft : exchangeOperator J j k * pairTerm J j k η n = pairTerm J j k η n := by
    change (Matrix.toLpLin 2 2 (exchangeMatrix j k) ∘ₗ Matrix.toLpLin 2 2 P) =
      Matrix.toLpLin 2 2 P
    rw [← Matrix.toLpLin_mul]
    exact congrArg (Matrix.toLpLin 2 2) hleftM
  have hright : pairTerm J j k η n * exchangeOperator J j k = pairTerm J j k η n := by
    change (Matrix.toLpLin 2 2 P ∘ₗ Matrix.toLpLin 2 2 (exchangeMatrix j k)) =
      Matrix.toLpLin 2 2 P
    rw [← Matrix.toLpLin_mul]
    exact congrArg (Matrix.toLpLin 2 2) hrightM
  constructor
  · change ((1 / 2 : ℂ) • (1 + exchangeOperator J j k)) *
      pairTerm J j k η n = pairTerm J j k η n
    calc
      _ = (1 / 2 : ℂ) • ((1 + exchangeOperator J j k) * pairTerm J j k η n) := by
        rw [smul_mul_assoc]
      _ = (1 / 2 : ℂ) • (pairTerm J j k η n + pairTerm J j k η n) := by
        rw [add_mul, one_mul, hleft]
      _ = (1 / 2 : ℂ) • ((2 : ℂ) • pairTerm J j k η n) := by rw [two_smul]
      _ = pairTerm J j k η n := by simp
  · change pairTerm J j k η n * ((1 / 2 : ℂ) • (1 + exchangeOperator J j k)) =
      pairTerm J j k η n
    calc
      _ = (1 / 2 : ℂ) • (pairTerm J j k η n * (1 + exchangeOperator J j k)) := by
        rw [mul_smul_comm]
      _ = (1 / 2 : ℂ) • (pairTerm J j k η n + pairTerm J j k η n) := by
        rw [mul_add, mul_one, hright]
      _ = (1 / 2 : ℂ) • ((2 : ℂ) • pairTerm J j k η n) := by rw [two_smul]
      _ = pairTerm J j k η n := by simp

end AKLT.W.H1M053
