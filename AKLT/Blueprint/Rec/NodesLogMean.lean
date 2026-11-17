module
public import AKLT.Blueprint.Rec.NodesResponse

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.Blueprint.Rec

/-- `e:rec-log-integral`, §7 lines 297–302. Integrate the reciprocal affine
denominator; split the diagonal before using log(b/a). -/
def ReciprocalIntegralStatement : Prop :=
  ∀ x y : ℝ, 0 < x → 0 < y →
    (logarithmicMean x y)⁻¹ = ∫ t in (0 : ℝ)..1, ((1 - t) * x + t * y)⁻¹

/-- `l:log-mean-bounds`, §7 lines 304–328. The x derivative of the
integrand is nonpositive because 5c≥3 and cA+B≤A+B. -/
def LogCoefficientMonoXStatement : Prop :=
  ∀ c x x' y : ℝ, 3 / 5 ≤ c → c ≤ 1 → 0 < x → x ≤ x' → 0 < y →
    1 / (3 * logarithmicMean (c * x') y) - 1 / (5 * logarithmicMean x' y) ≤
      1 / (3 * logarithmicMean (c * x) y) - 1 / (5 * logarithmicMean x y)

/-- `l:log-mean-bounds`, §7 lines 304–328. The y derivative has the
same sign. Work on a compact positive rectangle before integrating. -/
def LogCoefficientMonoYStatement : Prop :=
  ∀ c x y y' : ℝ, 3 / 5 ≤ c → c ≤ 1 → 0 < x → 0 < y → y ≤ y' →
    1 / (3 * logarithmicMean (c * x) y') - 1 / (5 * logarithmicMean x y') ≤
      1 / (3 * logarithmicMean (c * x) y) - 1 / (5 * logarithmicMean x y)

/-- `l:log-mean-bounds`, §7 lines 330–342. Exact finite geometric
remainder after eight odd powers; 0≤z≤t<1 is explicit. -/
def EightTermRemainderStatement : Prop :=
  ∀ t : ℝ, 0 < t → t < 1 →
    0 ≤ Real.log ((1 + t) / (1 - t)) - 2 * ∑ k ∈ Finset.range 8, t^(2*k+1) / (2*k+1 : ℝ) ∧
    Real.log ((1 + t) / (1 - t)) - 2 * ∑ k ∈ Finset.range 8, t^(2*k+1) / (2*k+1 : ℝ) ≤
      2 * t^17 / (17 * (1 - t^2))

/-- `l:log-mean-bounds`, §7 lines 330–342. Substitute t=(1-s)/(1+s),
use the lower remainder bound, and divide by positive 1-s. -/
def LogEnclosureLowerStatement : Prop :=
  ∀ s : ℚ, 0 < s → s < 1 → (logMeanLower s : ℝ) ≤ reciprocalLogMean s

/-- `l:log-mean-bounds`, §7 lines 330–342. The upper remainder bound
gives f_+; include rational-to-real coercions before clearing denominators. -/
def LogEnclosureUpperStatement : Prop :=
  ∀ s : ℚ, 0 < s → s < 1 → reciprocalLogMean s ≤ (logMeanUpper s : ℝ)

/-- `e:rec-log-table`, §7 lines 344–390. Exact rational endpoint rows. -/
def LogRationalRowsStatement : Prop :=
  ∀ straight : Bool,
    logMeanUpper ((116 / 125) * localThreshold straight) / 3 - logMeanLower (116 / 125) / 5 ≤
      alphaBound straight ∧
    logMeanUpper ((116 / 125) * localThreshold straight) / 3 ≤ betaBound straight ∧
    logMeanUpper (localThreshold straight) / 3 ≤ betaPrimeBound straight ∧
    0 < betaPrimeBound straight ∧ betaPrimeBound straight ≤ betaBound straight

theorem logRationalRows : LogRationalRowsStatement := by
  intro straight
  cases straight <;>
    norm_num [localThreshold, alphaBound, betaBound, betaPrimeBound,
      logMeanUpper, logMeanLower, Finset.sum_range_succ]

/-- `l:log-mean-bounds`, §7 lines 266–268. The diagonal is a definition,
so no limiting argument or division by log 1 is involved. -/
theorem reciprocalLogMean_one : reciprocalLogMean 1 = 1 := by
  norm_num [reciprocalLogMean, logarithmicMean]

/-- `l:response-typed`, §7 lines 512–515. The exact amended tables lie
below the retained crude majorants. -/
def TypedCrudeRowsStatement : Prop :=
  ∀ straight : Bool, alphaBound straight ≤ 18094 / 100000 ∧
    betaBound straight ≤ 36751 / 100000 ∧ betaPrimeBound straight ≤ 36751 / 100000

theorem typedCrudeRows : TypedCrudeRowsStatement := by
  intro straight
  cases straight <;> norm_num [alphaBound, betaBound, betaPrimeBound]

end AKLT.Blueprint.Rec
