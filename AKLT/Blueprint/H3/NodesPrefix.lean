import AKLT.Blueprint.H3.Positivity

noncomputable section
open scoped BigOperators
open AKLT.Defs
attribute [local instance] Classical.propDecidable

namespace AKLT.Blueprint.H3

/-- `l:prefix-domination`, lines 996–1003: a long first-hit trail has a surviving
length-twelve prefix. Restrict bond injectivity, and use 12<n to exclude a target hit at 12.
A hit at exactly twelve is thereby reserved for the short sum. -/
def LongTrailPrefixStatement : Prop :=
  ∀ X : PairType, ∀ d₀ : Compass, ∀ n : ℕ, 12 < n → ∀ w : DirectionWord n,
    ClosedTrail X w → FirstDirection w d₀ → SurvivingPrefix X d₀ (takeWord w 12)

/-- `l:prefix-domination`, lines 996–1006: unique concatenation without quotienting
prefix multiplicities. This elementary word equivalence is useful independently of trails. -/
def WordSplitStatement : Prop :=
  ∀ L r : ℕ, ∃ e : DirectionWord (L + r) ≃ (DirectionWord L × DirectionWord r),
    (∀ w, (e w).1 = takeWord w L) ∧
    (∀ P v, e.symm (P, v) = appendWords P v)

/-- Immediate finite-word equivalence used in prefix regrouping. -/
theorem wordSplit_proved : WordSplitStatement := by
  intro L r
  let e : DirectionWord (L + r) ≃ (DirectionWord L × DirectionWord r) :=
    { toFun := fun w => (takeWord w L, fun i => w ⟨L + i.val, by omega⟩)
      invFun := fun p => appendWords p.1 p.2
      left_inv := by
        intro w
        funext i
        by_cases hi : i.val < L
        · simp [appendWords, takeWord, hi, show i.val < L + r by omega]
        · simp [appendWords, hi, show L + (i.val - L) = i.val by omega]
      right_inv := by
        rintro ⟨P, v⟩
        apply Prod.ext
        · funext i
          simp [takeWord, appendWords, show i.val < L + r by omega]
        · funext i
          simp [appendWords, show ¬ L + i.val < L by omega] }
  exact ⟨e, fun _ => rfl, fun _ _ => rfl⟩

/-- `l:prefix-domination`, lines 996–1006: finite reindexing by prefix and suffix.
The explicit premise supplies each long trail's phase factorization. Reindex the finite
length/word sum by n=12+r and WordSplit; zero-length suffixes vanish for surviving prefixes.
No statement constant is used as a premise and both length endpoints are explicit. -/
def LongRowRegroupingStatement : Prop :=
  ∀ X : PairType, ∀ d₀ : Compass, ∀ R : ℕ, 12 < R →
    (∀ r : ℕ, ∃ e : DirectionWord (12 + r) ≃ (DirectionWord 12 × DirectionWord r),
      (∀ w, (e w).1 = takeWord w 12) ∧ (∀ P v, e.symm (P, v) = appendWords P v)) →
    (∀ n : ℕ, 12 < n → ∀ w : DirectionWord n, ClosedTrail X w →
      FirstDirection w d₀ → SurvivingPrefix X d₀ (takeWord w 12)) →
    (∀ n : ℕ, 12 < n → n ≤ R → ∀ w : DirectionWord n,
      ClosedTrail X w → FirstDirection w d₀ →
      closedContribution w = ∑ φ : Phase, prefixPhases (takeWord w 12) φ * truePhaseSuffix w 12 φ) →
    firstDirectionPartialRow X d₀ R = firstDirectionPartialRow X d₀ 12 +
      ∑ P : DirectionWord 12, if SurvivingPrefix X d₀ P then
        ∑ φ : Phase, prefixPhases P φ * trueContinuationSum X P φ (R - 12) else 0

/-- `l:prefix-domination`, lines 991–995: finite-cutoff monotonicity, also at cutoff zero. -/
theorem firstDirectionPartialRow_mono (X : PairType) (d₀ : Compass) {R S : ℕ} (hRS : R ≤ S) :
    firstDirectionPartialRow X d₀ R ≤ firstDirectionPartialRow X d₀ S := by
  classical
  apply Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.Icc_subset_Icc le_rfl hRS)
  intro n _ _
  apply Finset.sum_nonneg
  intro w _
  split_ifs
  · exact closedContribution_nonneg w
  · exact le_rfl

end AKLT.Blueprint.H3
