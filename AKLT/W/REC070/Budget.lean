import AKLT.Blueprint.Rec.NodesKernel

noncomputable section
open scoped BigOperators ENNReal
open AKLT.Defs
open AKLT.Blueprint.Rec

namespace AKLT.W.REC070

def RowLength (θ : ℝ) (X : PairType) (n : ℕ) : ℝ≥0∞ :=
  ∑ Y : PairType, ∑ s ∈ Finset.range (n + 2),
    ENNReal.ofReal (kernelLengthCoefficient X Y s n : ℝ) *
      ENNReal.ofReal (witnessReal Y) * ENNReal.ofReal (θ ^ (-(s : ℤ)))

def RowLengthError (CV q θ : ℝ) (X : PairType) (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal ((1 - θ) * witnessRatio *
    (18094 / 100000 + 2 * (36751 / 100000 : ℝ)) * CV *
    ((1 + q) / 2)^(-2 : ℤ) * (n : ℝ) * (n + 1 : ℝ) *
    (q / ((1 + q) / 2))^n * witnessReal X)

def RowError (CV q θ : ℝ) (X : PairType) : ℝ≥0∞ :=
  ENNReal.ofReal ((1 - θ) * transportB CV q * witnessReal X)

/-- Reindex the nonnegative row into finite length contributions. -/
def Residual_RowExpansion : Prop :=
  ∀ θ : ℝ, 0 < θ → ∀ X : PairType,
    (∑ Y : PairType, shiftedKernel θ X Y * ENNReal.ofReal (witnessReal Y)) =
      ∑' n : ℕ, RowLength θ X n

/-- One finite length's shift increment, using the H2 length envelope. -/
def Residual_LengthIncrement : Prop :=
  ∀ CV q : ℝ, OpenTrailBound CV q → ∀ θ : ℝ,
    (1 + q) / 2 < θ → θ ≤ 1 → ∀ X : PairType, ∀ n : ℕ,
      RowLength θ X n ≤ RowLength 1 X n + RowLengthError CV q θ X n

/-- The exact weighted geometric sum used by the transport budget. -/
def Residual_GeometricBudget : Prop :=
  ∀ CV q θ : ℝ, 0 ≤ CV → 0 < q → q < 1 → (1 + q) / 2 < θ → θ ≤ 1 →
    ∀ X : PairType,
      (∑' n : ℕ, RowLengthError CV q θ X n) ≤ RowError CV q θ X

theorem geometricBudget_proved : Residual_GeometricBudget := by
  intro CV q θ hCV hq0 hq1 hθ hθ1 X
  let b : ℝ := (1 + q) / 2
  let r : ℝ := q / b
  let K : ℝ := (1 - θ) * witnessRatio *
    (18094 / 100000 + 2 * (36751 / 100000 : ℝ)) * CV * b^(-2 : ℤ) * witnessReal X
  have hb : 0 < b := by dsimp [b]; linarith
  have hqB : q < b := by dsimp [b]; linarith
  have hr0 : 0 < r := div_pos hq0 hb
  have hr1 : r < 1 := (div_lt_one hb).2 hqB
  have hr : ‖r‖ < 1 := by rw [Real.norm_of_nonneg hr0.le]; exact hr1
  have hK : 0 ≤ K := by
    dsimp [K]
    have hH : 0 < witnessRatio := by
      norm_num [witnessRatio, witnessReal, kernelWitness]
    have hW : 0 < witnessReal X := by
      cases X <;> norm_num [witnessReal, kernelWitness]
    have hbpow : 0 < b ^ (-2 : ℤ) := zpow_pos hb _
    positivity
  have hs2 : Summable (fun n : ℕ => (n : ℝ)^2 * r^n) :=
    summable_pow_mul_geometric_of_norm_lt_one 2 hr
  have hs1 : Summable (fun n : ℕ => (n : ℝ) * r^n) := by
    simpa [pow_one] using summable_pow_mul_geometric_of_norm_lt_one 1 hr
  have hpoly : Summable (fun n : ℕ => (n : ℝ) * (n + 1 : ℝ) * r^n) := by
    convert hs2.add hs1 using 1
    ext n
    ring
  have hseries :
      (∑' n : ℕ, (n : ℝ) * (n + 1 : ℝ) * r^n) = 2 * r / (1 - r)^3 := by
    have hsplit :
        (fun n : ℕ => (n : ℝ) * (n + 1 : ℝ) * r^n) =
          (fun n : ℕ => (n : ℝ)^2 * r^n + (n : ℝ) * r^n) := by
      funext n
      ring
    rw [hsplit, hs2.tsum_add hs1,
      tsum_sq_mul_geometric_of_norm_lt_one hr,
      tsum_coe_mul_geometric_of_norm_lt_one hr]
    have hden : 1 - r ≠ 0 := ne_of_gt (sub_pos.mpr hr1)
    field_simp
    ring
  have hterm : ∀ n : ℕ,
      RowLengthError CV q θ X n = ENNReal.ofReal (K * ((n : ℝ) * (n + 1 : ℝ) * r^n)) := by
    intro n
    simp only [RowLengthError, b, r, K]
    congr 1
    ring
  have htotal : (∑' n : ℕ, RowLengthError CV q θ X n) =
      ENNReal.ofReal (K * (∑' n : ℕ, (n : ℝ) * (n + 1 : ℝ) * r^n)) := by
    calc
      (∑' n : ℕ, RowLengthError CV q θ X n) =
          ∑' n : ℕ, ENNReal.ofReal (K * ((n : ℝ) * (n + 1 : ℝ) * r^n)) := by
            congr 1
            funext n
            exact hterm n
      _ = ENNReal.ofReal (∑' n : ℕ, K * ((n : ℝ) * (n + 1 : ℝ) * r^n)) :=
        (ENNReal.ofReal_tsum_of_nonneg
          (fun n => mul_nonneg hK (by positivity)) (hpoly.mul_left K)).symm
      _ = ENNReal.ofReal (K * (∑' n : ℕ, (n : ℝ) * (n + 1 : ℝ) * r^n)) := by
        rw [hpoly.tsum_mul_left]
  rw [htotal]
  rw [hseries]
  apply ENNReal.ofReal_le_ofReal
  have hBdef : transportB CV q = 2 * witnessRatio *
      (18094 / 100000 + 2 * (36751 / 100000 : ℝ)) * CV * b^(-2 : ℤ) * r / (1 - r)^3 := by
    simp [transportB, b, r]
  change K * (2 * r / (1 - r)^3) ≤
    (1 - θ) * transportB CV q * witnessReal X
  rw [hBdef]
  dsimp [K]
  ring_nf
  exact le_rfl

theorem main_of_residuals (hExpand : Residual_RowExpansion)
    (hIncrement : Residual_LengthIncrement) :
    AKLT.Blueprint.Rec.WitnessPerturbationStatement := by
  intro CV q hOpen θ ρ hθ hθ1 hρ hBudget X hBase
  rcases hOpen with ⟨hCV, hq0, hq1, hOpen⟩
  have htheta0 : 0 < θ := by
    have hbq : 0 < (1 + q) / 2 := by linarith
    linarith
  have hRowLe :
      (∑ Y : PairType, shiftedKernel θ X Y * ENNReal.ofReal (witnessReal Y)) ≤
      (∑ Y : PairType, shiftedKernel 1 X Y * ENNReal.ofReal (witnessReal Y)) +
        RowError CV q θ X := by
    rw [hExpand θ htheta0 X, hExpand 1 (by norm_num) X]
    calc
      (∑' n : ℕ, RowLength θ X n) ≤
          ∑' n : ℕ, (RowLength 1 X n + RowLengthError CV q θ X n) := by
            apply ENNReal.tsum_le_tsum
            intro n
            exact hIncrement CV q ⟨hCV, hq0, hq1, hOpen⟩ θ hθ hθ1 X n
      _ = (∑' n : ℕ, RowLength 1 X n) +
          ∑' n : ℕ, RowLengthError CV q θ X n := by
            rw [ENNReal.tsum_add]
      _ ≤ (∑' n : ℕ, RowLength 1 X n) + RowError CV q θ X := by
            calc
              _ = (∑' n : ℕ, RowLengthError CV q θ X n) +
                    (∑' n : ℕ, RowLength 1 X n) := by rw [add_comm]
              _ ≤ RowError CV q θ X + (∑' n : ℕ, RowLength 1 X n) :=
                add_le_add_left (geometricBudget_proved CV q θ
                  (le_trans (by norm_num) hCV) hq0 hq1 hθ hθ1 X) _
              _ = (∑' n : ℕ, RowLength 1 X n) + RowError CV q θ X := by rw [add_comm]
  have hXpos : 0 < witnessReal X := by
    cases X <;> norm_num [witnessReal, kernelWitness]
  have hRow :
      (∑ Y : PairType, shiftedKernel θ X Y * ENNReal.ofReal (witnessReal Y)) ≤
        ENNReal.ofReal (ρ * witnessReal X) := by
    calc
      (∑ Y : PairType, shiftedKernel θ X Y * ENNReal.ofReal (witnessReal Y)) ≤
          (∑ Y : PairType, shiftedKernel 1 X Y * ENNReal.ofReal (witnessReal Y)) +
            RowError CV q θ X := hRowLe
      _ ≤ ENNReal.ofReal ((kernelRho : ℝ) * witnessReal X) +
            ENNReal.ofReal ((1 - θ) * transportB CV q * witnessReal X) :=
        add_le_add hBase (by rfl)
      _ = ENNReal.ofReal (((kernelRho : ℝ) + (1 - θ) * transportB CV q) * witnessReal X) := by
        have hkr : 0 ≤ (kernelRho : ℝ) := by norm_num [kernelRho]
        have hB : 0 < transportB CV q := by
          have hb : 0 < (1 + q) / 2 := by linarith
          have hr1 : q / ((1 + q) / 2) < 1 := by
            rw [div_lt_one hb]
            linarith
          have hratio : 0 < witnessRatio := by
            norm_num [witnessRatio, witnessReal, kernelWitness]
          unfold transportB
          dsimp
          positivity
        have hleft : 0 ≤ (kernelRho : ℝ) * witnessReal X :=
          mul_nonneg hkr hXpos.le
        have htr : 0 ≤ (1 - θ) * transportB CV q * witnessReal X :=
          mul_nonneg (mul_nonneg (sub_nonneg.mpr hθ1) hB.le) hXpos.le
        rw [← ENNReal.ofReal_add hleft htr]
        congr 1
        ring
      _ ≤ ENNReal.ofReal (ρ * witnessReal X) := by
        apply ENNReal.ofReal_le_ofReal
        exact mul_le_mul_of_nonneg_right hBudget hXpos.le
  exact hRow

end AKLT.W.REC070
