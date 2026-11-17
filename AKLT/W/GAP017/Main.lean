module
public import AKLT.W.GAP017.Tensorization

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Gap

namespace AKLT.W.GAP017

/-- Density comparison with exactly one ratio of the positive density bounds. -/
theorem main : AKLT.Blueprint.Gap.DensityComparisonStatement := by
  classical
  intro ι hι hdec S hSfin hSnonempty π μ hπ hμ m M hm hM hbounds
  let q : Weight (Config S) := fun σ => ∏ x, π x (σ x)
  have hqprob : Probability q :=
    ⟨fun σ => le_of_lt ((product_probability π hπ).1 σ),
      (product_probability π hπ).2⟩
  have hμprob : Probability μ := ⟨fun σ => le_of_lt (hμ.1 σ), hμ.2⟩
  have hdir (f : Config S → ℂ) :
      m * dirichlet q f ≤ dirichlet μ f := by
    unfold dirichlet
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x hx
    let U : Finset ι := {x}
    let h : Config S → ℂ := conditionalExpectation μ U f
    have hh : ∀ σ τ, AgreeOutside U σ τ → h σ = h τ := by
      intro σ τ hστ
      exact conditionalExpectation_eq_of_agree μ U f σ τ hστ
    have hmin := product_singleton_min π hπ x f h hh
    have hcomp :
        m * (∑ σ, q σ * Complex.normSq (f σ - h σ)) ≤
          ∑ σ, μ σ * Complex.normSq (f σ - h σ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro σ hσ
      have hb := hbounds σ
      have hs := Complex.normSq_nonneg (f σ - h σ)
      dsimp [q] at hb ⊢
      nlinarith [mul_nonneg (le_of_lt hm) hs]
    calc
      m * blockDirichlet q U f ≤
          m * (∑ σ, q σ * Complex.normSq (f σ - h σ)) :=
        mul_le_mul_of_nonneg_left hmin (le_of_lt hm)
      _ ≤ ∑ σ, μ σ * Complex.normSq (f σ - h σ) := hcomp
      _ = blockDirichlet μ U f := by rfl
  have hvar (f : Config S → ℂ) : variance μ f ≤ M * variance q f := by
    have hmeanμ := weighted_sq_decomp μ hμprob f (complexMean q f)
    have hmeanq := weighted_sq_decomp q hqprob f (complexMean q f)
    have hle :
        (∑ σ, μ σ * Complex.normSq (f σ - complexMean q f)) ≤
          M * (∑ σ, q σ * Complex.normSq (f σ - complexMean q f)) := by
      calc
        (∑ σ, μ σ * Complex.normSq (f σ - complexMean q f)) ≤
            ∑ σ, M * (q σ * Complex.normSq (f σ - complexMean q f)) := by
              apply Finset.sum_le_sum
              intro σ hσ
              have hb := (hbounds σ).2
              have hs := Complex.normSq_nonneg (f σ - complexMean q f)
              dsimp [q] at hb ⊢
              nlinarith [mul_nonneg (le_of_lt hM) hs]
        _ = M * (∑ σ, q σ * Complex.normSq (f σ - complexMean q f)) := by
              rw [Finset.mul_sum]
    have hzero : Complex.normSq (complexMean q f - complexMean q f) = 0 := by simp
    rw [hmeanμ] at hle
    rw [hmeanq, hzero] at hle
    have hs := Complex.normSq_nonneg (complexMean μ f - complexMean q f)
    dsimp [variance] at hle ⊢
    nlinarith
  constructor
  · intro f
    exact ⟨hdir f, hvar f⟩
  · intro f
    have hprod' : variance q f ≤ dirichlet q f := by
      have hprod : 1 * variance q f ≤ dirichlet q f := product_tensorization π hπ f
      simpa only [one_mul] using hprod
    have hvar' := hvar f
    have hscaled : (m / M) * variance μ f ≤ m * variance q f := by
      calc
        (m / M) * variance μ f ≤ (m / M) * (M * variance q f) :=
          mul_le_mul_of_nonneg_left hvar' (le_of_lt (div_pos hm hM))
        _ = m * variance q f := by field_simp
    calc
      (m / M) * variance μ f ≤ m * variance q f := hscaled
      _ ≤ m * dirichlet q f := mul_le_mul_of_nonneg_left hprod' (le_of_lt hm)
      _ ≤ dirichlet μ f := hdir f

end AKLT.W.GAP017
