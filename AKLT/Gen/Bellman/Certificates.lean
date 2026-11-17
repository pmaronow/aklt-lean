module
public import Mathlib

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

/-!
# Soundness of scaled finite row inequalities

This lemma explains the two independent scales of a stationary certificate. Candidate values
are `v / V`, coefficient ceilings are `p / D`, and the checked inequality is entirely natural
number arithmetic. It applies to both free rows and stored stationary rows. No data or checker
is included here.
-/

namespace AKLT.Gen.Bellman

open scoped BigOperators
open scoped ENNReal

variable {E : Type*}

/-- An integer row check and coefficient ceilings imply the exact real Bellman row. -/
theorem scaled_row_sound (edges : Finset E) (t : E → ℝ) (p v : E → ℕ)
    (D V u : ℕ) (hD : 0 < D) (hV : 0 < V)
    (hceil : ∀ e ∈ edges, t e ≤ (p e : ℝ) / (D : ℝ))
    (hcheck : ∑ e ∈ edges, p e * v e ≤ D * u) :
    (∑ e ∈ edges, t e * ((v e : ℝ) / (V : ℝ))) ≤ (u : ℝ) / (V : ℝ) := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hVr : (0 : ℝ) < V := by exact_mod_cast hV
  have hc : (∑ e ∈ edges, (p e : ℝ) * (v e : ℝ)) ≤ (D : ℝ) * (u : ℝ) := by
    exact_mod_cast hcheck
  calc
    (∑ e ∈ edges, t e * ((v e : ℝ) / (V : ℝ))) ≤
        ∑ e ∈ edges, ((p e : ℝ) / (D : ℝ)) * ((v e : ℝ) / (V : ℝ)) := by
      apply Finset.sum_le_sum
      intro e he
      exact mul_le_mul_of_nonneg_right (hceil e he) (by positivity)
    _ = (∑ e ∈ edges, (p e : ℝ) * (v e : ℝ)) / ((D : ℝ) * (V : ℝ)) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro e _
      ring
    _ ≤ ((D : ℝ) * (u : ℝ)) / ((D : ℝ) * (V : ℝ)) :=
      div_le_div_of_nonneg_right hc (by positivity)
    _ = (u : ℝ) / (V : ℝ) := by
      field_simp

/-- The same checked row directly bounds `ENNReal` coefficients and values. -/
theorem scaled_ennreal_row_sound (edges : Finset E) (t : E → ℝ≥0∞) (p v : E → ℕ)
    (D V u : ℕ) (hD : 0 < D) (hV : 0 < V)
    (hceil : ∀ e ∈ edges, t e ≤ (p e : ℝ≥0∞) / (D : ℝ≥0∞))
    (hcheck : ∑ e ∈ edges, p e * v e ≤ D * u) :
    (∑ e ∈ edges, t e * ((v e : ℝ≥0∞) / (V : ℝ≥0∞))) ≤
      (u : ℝ≥0∞) / (V : ℝ≥0∞) := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hVr : (0 : ℝ) < V := by exact_mod_cast hV
  have hc := ENNReal.ofReal_le_ofReal
    (scaled_row_sound edges (fun e => (p e : ℝ) / (D : ℝ)) p v D V u hD hV
      (fun _ _ => le_rfl) hcheck)
  have heq : ENNReal.ofReal (∑ e ∈ edges,
      ((p e : ℝ) / (D : ℝ)) * ((v e : ℝ) / (V : ℝ))) =
      ∑ e ∈ edges, ((p e : ℝ≥0∞) / (D : ℝ≥0∞)) *
        ((v e : ℝ≥0∞) / (V : ℝ≥0∞)) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
    apply Finset.sum_congr rfl
    intro e _
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_div_of_pos hDr,
      ENNReal.ofReal_div_of_pos hVr]
    simp
  rw [heq, ENNReal.ofReal_div_of_pos hVr] at hc
  simp only [ENNReal.ofReal_natCast] at hc
  apply le_trans _ hc
  apply Finset.sum_le_sum
  intro e he
  exact mul_le_mul (hceil e he) le_rfl (by positivity) (by positivity)

end AKLT.Gen.Bellman
