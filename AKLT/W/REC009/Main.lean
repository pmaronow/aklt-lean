import AKLT.Blueprint.Rec.NodesResponse

noncomputable section
open scoped BigOperators

namespace AKLT.W.REC009

private lemma atanh_crude (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    Real.log ((1 + t) / (1 - t)) ≤
      2 * (t + t ^ 3 / 3 + t ^ 5 / (5 * (1 - t ^ 2))) := by
  let f : ℕ → ℝ := fun k => 2 * (1 / (2 * (k : ℝ) + 1)) * t ^ (2 * k + 1)
  let g : ℕ → ℝ := fun k => (2 / 5) * t ^ 5 * (t ^ 2) ^ k
  have ht2 : 0 ≤ t ^ 2 := sq_nonneg t
  have ht2one : t ^ 2 < 1 := by
    nlinarith [mul_pos (sub_pos.mpr ht1) (add_pos ht0 zero_lt_one)]
  have hseries := Real.hasSum_log_sub_log_of_abs_lt_one
    (x := t) (by rw [abs_of_pos ht0]; exact ht1)
  have hgeom : HasSum (fun k : ℕ => (t ^ 2) ^ k) (1 - t ^ 2)⁻¹ :=
    hasSum_geometric_of_lt_one ht2 ht2one
  have hgs : Summable g := by
    simpa [g] using hgeom.summable.mul_left ((2 / 5 : ℝ) * t ^ 5)
  have hterm (k : ℕ) : f (k + 2) ≤ g k := by
    have heq : f (k + 2) = (2 / (2 * (k : ℝ) + 5)) * (t ^ 5 * (t ^ 2) ^ k) := by
      simp only [f, Nat.cast_add]
      have hexp : 2 * (k + 2) + 1 = 5 + 2 * k := by omega
      rw [hexp, pow_add, pow_mul]
      push_cast
      ring
    rw [heq]
    have hden : 0 < 2 * (k : ℝ) + 5 := by positivity
    have hfrac : (2 : ℝ) / (2 * (k : ℝ) + 5) ≤ 2 / 5 := by
      rw [div_le_div_iff₀ hden (by norm_num : (0 : ℝ) < 5)]
      nlinarith
    change (2 / (2 * (k : ℝ) + 5)) * (t ^ 5 * (t ^ 2) ^ k) ≤
      (2 / 5) * t ^ 5 * (t ^ 2) ^ k
    calc
      (2 / (2 * (k : ℝ) + 5)) * (t ^ 5 * (t ^ 2) ^ k) ≤
          (2 / 5) * (t ^ 5 * (t ^ 2) ^ k) :=
        mul_le_mul_of_nonneg_right hfrac (by positivity)
      _ = (2 / 5) * t ^ 5 * (t ^ 2) ^ k := by ring
  have htailSummable : Summable (fun k => f (k + 2)) := by
    apply Summable.of_norm_bounded hgs
    intro k
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ f (k + 2))]
    exact hterm k
  have htail := htailSummable.tsum_le_tsum hterm hgs
  have htail' : (∑' k : ℕ, f (k + 2)) ≤ 2 * t ^ 5 / (5 * (1 - t ^ 2)) := by
    calc
      (∑' k : ℕ, f (k + 2)) ≤ ∑' k : ℕ, g k := htail
      _ = (2 / 5 : ℝ) * t ^ 5 * (1 - t ^ 2)⁻¹ := by
        calc
          (∑' k : ℕ, g k) = ((2 / 5 : ℝ) * t ^ 5) * ∑' k : ℕ, (t ^ 2) ^ k := by
            rw [show (fun k : ℕ => g k) = fun k => ((2 / 5 : ℝ) * t ^ 5) * (t ^ 2) ^ k by
              funext k
              simp [g, mul_assoc]]
            rw [tsum_mul_left]
          _ = (2 / 5 : ℝ) * t ^ 5 * (1 - t ^ 2)⁻¹ := by rw [hgeom.tsum_eq]
      _ = 2 * t ^ 5 / (5 * (1 - t ^ 2)) := by field_simp
  have hdecomp := hseries.summable.sum_add_tsum_nat_add 2
  have hfirst : (∑ k ∈ Finset.range 2, f k) = 2 * (t + t ^ 3 / 3) := by
    norm_num [f, Finset.sum_range_succ]
    ring_nf
  have hlogratio : Real.log ((1 + t) / (1 - t)) = Real.log (1 + t) - Real.log (1 - t) := by
    rw [Real.log_div (ne_of_gt (by linarith : 0 < 1 + t))
      (ne_of_gt (sub_pos.mpr ht1))]
  calc
    Real.log ((1 + t) / (1 - t)) = ∑' k : ℕ, f k := by rw [hlogratio]; exact hseries.tsum_eq.symm
    _ = (∑ k ∈ Finset.range 2, f k) + ∑' k : ℕ, f (k + 2) := hdecomp.symm
    _ ≤ 2 * (t + t ^ 3 / 3) + 2 * t ^ 5 / (5 * (1 - t ^ 2)) := by
      rw [hfirst]
      exact add_le_add le_rfl htail'
    _ = 2 * (t + t ^ 3 / 3 + t ^ 5 / (5 * (1 - t ^ 2))) := by ring

theorem main : AKLT.Blueprint.Rec.CrudeLogEnclosureStatement := by
  intro s hs0 hs1
  let x : ℝ := s
  let t : ℝ := (1 - x) / (1 + x)
  have hx0 : 0 < x := by dsimp [x]; exact_mod_cast hs0
  have hx1 : x < 1 := by dsimp [x]; exact_mod_cast hs1
  have ht0 : 0 < t := by
    dsimp [t]
    exact div_pos (sub_pos.mpr hx1) (by positivity)
  have ht1 : t < 1 := by
    dsimp [t]
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 1 + x)).2
    linarith
  have hratio : (1 + t) / (1 - t) = x⁻¹ := by
    dsimp [t]
    field_simp [ne_of_gt hx0]
    ring
  have hlog : Real.log ((1 + t) / (1 - t)) = -Real.log x := by
    rw [hratio, Real.log_inv]
  have hlogbound := atanh_crude t ht0 ht1
  rw [hlog] at hlogbound
  have hmean : AKLT.Defs.reciprocalLogMean x = -Real.log x / (1 - x) := by
    have hlogx : Real.log x ≠ 0 := ne_of_lt (Real.log_neg hx0 hx1)
    simp [AKLT.Defs.reciprocalLogMean, AKLT.Defs.logarithmicMean,
      ne_of_lt hx1, Real.log_one]
    field_simp [hlogx, ne_of_gt (sub_pos.mpr hx1), ne_of_lt (sub_lt_zero.mpr hx1)]; ring
  have hden : 0 < 1 - x := by linarith
  have hrealbound : AKLT.Defs.reciprocalLogMean x ≤
      (2 / (1 - x)) * (t + t ^ 3 / 3 + t ^ 5 / (5 * (1 - t ^ 2))) := by
    rw [hmean]
    calc
      -Real.log x / (1 - x) ≤ (2 * (t + t ^ 3 / 3 + t ^ 5 / (5 * (1 - t ^ 2)))) / (1 - x) :=
        div_le_div_of_nonneg_right hlogbound (le_of_lt hden)
      _ = (2 / (1 - x)) * (t + t ^ 3 / 3 + t ^ 5 / (5 * (1 - t ^ 2))) := by ring
  have hcast : (AKLT.Blueprint.Rec.crudeLogUpper s : ℝ) =
      (2 / (1 - x)) * (t + t ^ 3 / 3 + t ^ 5 / (5 * (1 - t ^ 2))) := by
    dsimp [AKLT.Blueprint.Rec.crudeLogUpper, t, x]
    push_cast
    ring
  rw [hcast]
  exact hrealbound

end AKLT.W.REC009
