module
public import AKLT.Cert.H2.Growth
public import AKLT.Cert.H2.Finite

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.Cert.H2

set_option autoImplicit false
set_option maxHeartbeats 2000000
attribute [local instance] Classical.propDecidable

theorem rate_pos : (0 : ℚ) < certifiedRate := by norm_num [certifiedRate]
theorem rate_lt_one : certifiedRate < (1 : ℚ) := by norm_num [certifiedRate]
theorem cv_numeric : 6 * (200 / (187 * certifiedRate)) ^ 6 < (10 : ℚ) := by
  norm_num [certifiedRate]

theorem scaled_total (r : ℕ) :
    (openTrailTotal r (0, 0) .east : ℝ) * (certifiedRate : ℝ) ^ (-(r : ℤ)) ≤
      (200 / (187 * (certifiedRate : ℝ))) ^ r := by
  have hq : (0 : ℝ) < certifiedRate := by exact_mod_cast rate_pos
  rw [zpow_neg, zpow_natCast, ← div_eq_mul_inv]
  calc
    (openTrailTotal r (0, 0) .east : ℝ) / (certifiedRate : ℝ) ^ r ≤
        ((passageFactor false : ℚ) : ℝ) ^ r / (certifiedRate : ℝ) ^ r := by
      apply div_le_div_of_nonneg_right _ (pow_nonneg hq.le r)
      exact_mod_cast total_majorant r (0, 0) .east
    _ = (200 / (187 * (certifiedRate : ℝ))) ^ r := by
      rw [← div_pow]
      congr 1
      norm_num [passageFactor, localThreshold]
      ring

theorem cv_base (v : MemoryWindow 6 → ℝ) (_hv : ∀ ω, 0 < v ω)
    (hr : memoryWitnessRatio v ≤ 6) :
    memoryBaseConstant 6 (certifiedRate : ℝ) v ≤
      6 * (200 / (187 * (certifiedRate : ℝ))) ^ 6 ∧
    memoryBaseConstant 6 (certifiedRate : ℝ) v < 10 := by
  let b : ℝ := 200 / (187 * (certifiedRate : ℝ))
  have hb : 1 ≤ b := by norm_num [b, certifiedRate]
  have hb0 : 0 ≤ b ^ 6 := pow_nonneg (by linarith) _
  have hnum : 6 * b ^ 6 < 10 := by
    dsimp only [b]
    exact_mod_cast cv_numeric
  have hC : memoryBaseConstant 6 (certifiedRate : ℝ) v ≤ 6 * b ^ 6 := by
    unfold memoryBaseConstant
    apply max_le
    · apply csSup_le
      · exact ⟨1, 0, by norm_num, by simp⟩
      · rintro r ⟨j, hj, rfl⟩
        have hp : b ^ j ≤ b ^ 6 := pow_le_pow_right₀ hb (by omega)
        exact (scaled_total j).trans (hp.trans (by nlinarith))
    · have ht := scaled_total 6
      have ht0 : 0 ≤ (openTrailTotal 6 (0, 0) .east : ℝ) * (certifiedRate : ℝ) ^ (-(6 : ℤ)) := by
        apply mul_nonneg
        · exact_mod_cast total_nonneg 6 (0, 0) .east
        · exact zpow_nonneg (by exact_mod_cast rate_pos.le) _
      calc
        memoryWitnessRatio v * (openTrailTotal 6 (0, 0) .east : ℝ) *
            (certifiedRate : ℝ) ^ (-(6 : ℤ)) =
          memoryWitnessRatio v * ((openTrailTotal 6 (0, 0) .east : ℝ) *
            (certifiedRate : ℝ) ^ (-(6 : ℤ))) := by ring
        _ ≤ 6 * ((openTrailTotal 6 (0, 0) .east : ℝ) *
            (certifiedRate : ℝ) ^ (-(6 : ℤ))) := mul_le_mul_of_nonneg_right hr ht0
        _ ≤ 6 * b ^ 6 := mul_le_mul_of_nonneg_left ht (by norm_num)
  exact ⟨hC, hC.trans_lt hnum⟩

theorem h2_of_test (ht : AKLT.Blueprint.Top.H2TestStatement) :
    AKLT.Blueprint.Top.H2Statement := by
  obtain ⟨_, _, _, v, lo, hi, hlo, hbounds, hlow, hhigh, _, hratio, _, hrows, _⟩ := ht
  let V : MemoryWindow 6 → ℝ := fun ω => v ω
  have hv : ∀ ω, 0 < V ω := by
    intro ω
    have hh : 0 < v ω := hlo.trans_le (hbounds ω).1
    dsimp only [V]
    exact_mod_cast hh
  have hs : sSup (Set.range V) = (hi : ℝ) := by
    apply le_antisymm
    · apply csSup_le (Set.range_nonempty V)
      rintro r ⟨ω, rfl⟩
      dsimp only [V]
      exact_mod_cast (hbounds ω).2
    · obtain ⟨ω, hω⟩ := hhigh
      apply le_csSup (Set.finite_range V).bddAbove
      exact ⟨ω, by dsimp [V]; rw [hω]⟩
  have hi' : sInf (Set.range V) = (lo : ℝ) := by
    apply le_antisymm
    · obtain ⟨ω, hω⟩ := hlow
      apply csInf_le (Set.finite_range V).bddBelow
      exact ⟨ω, by dsimp [V]; rw [hω]⟩
    · apply le_csInf (Set.range_nonempty V)
      rintro r ⟨ω, rfl⟩
      dsimp only [V]
      exact_mod_cast (hbounds ω).1
  have hratio' : memoryWitnessRatio V ≤ 6 := by
    unfold memoryWitnessRatio
    rw [hs, hi']
    exact le_of_lt (by exact_mod_cast hratio)
  have hw : ∀ ω, (∑ ω', (memoryMatrix 6 ω ω' : ℝ) * V ω') ≤
      (certifiedRate : ℝ) * V ω := by
    intro ω
    have hp : (0 : ℚ) < v ω := by exact_mod_cast hlo.trans_le (hbounds ω).1
    have hh := (div_le_iff₀ hp).mp (hrows ω)
    dsimp only [V]
    exact_mod_cast hh
  have hq : (0 : ℝ) < certifiedRate := by exact_mod_cast rate_pos
  have hq1 : (certifiedRate : ℝ) < 1 := by exact_mod_cast rate_lt_one
  exact (alm 6 (by norm_num)).2 V hv _ hq hq1 hw |>.2 10 (cv_base V hv hratio').2.le

/-- The complete Top base-constant contract. -/
theorem h2CV : AKLT.Blueprint.Top.H2CVStatement := by
  refine ⟨?_, cv_numeric, cv_base, h2_of_test⟩
  intro u incoming r _
  exact total_majorant r u incoming

/-- The unconditional (H2) input with the selected exact rate and C_V = 10. -/
theorem h2 : AKLT.Blueprint.Top.H2Statement := h2_of_test h2Test

end AKLT.Cert.H2
