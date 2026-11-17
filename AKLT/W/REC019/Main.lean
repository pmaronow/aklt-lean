module
public import AKLT.W.REC019.LogMean
public import AKLT.W.REC019.FreePositive
public import AKLT.W.REC019.NetworkBounds
public import AKLT.W.REC019.LocalBound
public import AKLT.W.REC019.DepartureGeometry
public import AKLT.W.REC019.Conditioning
public import AKLT.W.REC019.R4.Main

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open AKLT.Defs
open AKLT.Blueprint.Rec

namespace AKLT.W.REC019

/-- The three-spin conditional-mean lower bound, before any logarithms. -/
def Residual_TripleLower : Prop :=
  ∀ a : Departure, a.D.status a.y = .U → ∀ f g : Plane,
    a.D.presentNeighbours a.y = {a.o, f, g} → a.o ≠ f → a.o ≠ g → f ≠ g →
    -(27 / 50 : ℝ) ≤
      removedPairMean a.D a.τ true a.y f g + removedPairMean a.D a.τ true a.y f a.o +
        removedPairMean a.D a.τ true a.y g a.o

/-- The two-spin conditional-mean upper estimate in the departure-deleted network. -/
def Residual_PairUpper : Prop :=
  ∀ a : Departure, a.D.status a.y = .U → ∀ f g : Plane,
    a.D.presentNeighbours a.y = {a.o, f, g} → a.o ≠ f → a.o ≠ g → f ≠ g →
    ∀ b : Bool, removedPairMean a.D a.τ b a.y f g ≤ 9 / 25

/-- The remaining concrete-network conditioning bridge. The three removed pair
means must come from one common finite mixture of independent conditional
means. A zero total weight is permitted, matching the real quotient convention. -/
def Residual_ConditionalMixture : Prop :=
  ∀ a : Departure, a.D.status a.y = .U → ∀ f g : Plane,
    a.D.presentNeighbours a.y = {a.o, f, g} → a.o ≠ f → a.o ≠ g → f ≠ g →
    ∀ b : Bool, ∃ n : ℕ, ∃ w : Fin n → ℝ, ∃ m : Fin n → Fin 3 → Vec3,
      (∀ σ, 0 ≤ w σ) ∧ (∀ σ i, normSq (m σ i) ≤ 9 / 25) ∧
      removedPairMean a.D a.τ b a.y f g = mixturePair w m 0 1 ∧
      removedPairMean a.D a.τ b a.y f a.o = mixturePair w m 0 2 ∧
      removedPairMean a.D a.τ b a.y g a.o = mixturePair w m 1 2

theorem residuals_of_conditional_mixture (h : Residual_ConditionalMixture) :
    Residual_TripleLower ∧ Residual_PairUpper := by
  constructor
  · intro a hU f g hN hof hog hfg
    obtain ⟨n, w, m, hw, hm, h01, h02, h12⟩ := h a hU f g hN hof hog hfg true
    rw [h01, h02, h12]
    exact mixture_triple_lower w m hw hm
  · intro a hU f g hN hof hog hfg b
    obtain ⟨n, w, m, hw, hm, h01, h02, h12⟩ := h a hU f g hN hof hog hfg b
    rw [h01]
    exact (mixture_pair_bounds w m hw hm 0 1).2

/-- All analytic and rational steps of the alpha estimate, for arbitrary real
arguments satisfying the required moment intervals. -/
theorem alpha_bound_of_intervals {Iτ I₀ Jτ J₀ : ℝ}
    (hIτ : 41 / 50 ≤ Iτ) (hI₀ : 1 ≤ I₀)
    (hJτp : 0 < Jτ) (hJ₀p : 0 < J₀)
    (hJτ' : Jτ ≤ 134 / 125) (hJ₀' : J₀ ≤ 134 / 125) :
    1 / (3 * logarithmicMean Iτ I₀) - 1 / (5 * logarithmicMean Jτ J₀) ≤
      (18094 / 100000 : ℝ) := by
  have hIτp : 0 < Iτ := by linarith
  have hI₀p : 0 < I₀ := by linarith
  have hLJp := logMean_positive hJτp hJ₀p
  have hLIlower := logMean_monotone (by norm_num : (0 : ℝ) < 41 / 50) hIτ
    (by norm_num : (0 : ℝ) < 1) hI₀
  have hLJupper := logMean_le_upper hJτp hJ₀p hJτ' hJ₀'
  have hβ : 1 / (3 * logarithmicMean Iτ I₀) ≤ (367502 / 1000000 : ℝ) := by
    calc
      _ ≤ 1 / (3 * logarithmicMean (41 / 50) 1) := by
        apply one_div_le_one_div_of_le
        · exact mul_pos (by norm_num) (logMean_positive (by norm_num) (by norm_num))
        · exact mul_le_mul_of_nonneg_left hLIlower (by norm_num)
      _ ≤ _ := reciprocal_logMean_41_50
  have hrecip : (25 / 134 : ℝ) ≤ 1 / (5 * logarithmicMean Jτ J₀) := by
    apply (le_div_iff₀ (mul_pos (by norm_num) hLJp)).mpr
    nlinarith
  calc
    _ ≤ 367502 / 1000000 - 25 / 134 := sub_le_sub hβ hrecip
    _ ≤ _ := by norm_num

/-- The original leaf follows from two purely finite moment estimates. The
free positivity, logarithmic-mean facts, and exact coefficient checks are proved. -/
theorem main_of_residuals (hT : Residual_TripleLower) (hP : Residual_PairUpper) :
    AKLT.Blueprint.Rec.AlphaUniformStatement := by
  intro a hU f g hN hof hog hfg
  have hTτ := hT a hU f g hN hof hog hfg
  have hPτ := hP a hU f g hN hof hog hfg true
  have hP₀ := hP a hU f g hN hof hog hfg false
  have hfg₀ := free_removedPairMean_nonnegative a.D a.τ a.y f g
  have hfo₀ := free_removedPairMean_nonnegative a.D a.τ a.y f a.o
  have hgo₀ := free_removedPairMean_nonnegative a.D a.τ a.y g a.o
  have hIτ : 41 / 50 ≤ responseI a.D a.τ true a.y a.o f g := by
    unfold responseI
    linarith
  have hI₀ : 1 ≤ responseI a.D a.τ false a.y a.o f g := by
    unfold responseI
    linarith
  have hJτ := responseJ_positive a.D a.τ true a.y f g
  have hJ₀ := responseJ_positive a.D a.τ false a.y f g
  have hJτ' : responseJ a.D a.τ true a.y f g ≤ 134 / 125 := by
    unfold responseJ
    linarith
  have hJ₀' : responseJ a.D a.τ false a.y f g ≤ 134 / 125 := by
    unfold responseJ
    linarith
  exact alpha_bound_of_intervals hIτ hI₀ hJτ hJ₀ hJτ' hJ₀'

theorem main_of_conditional_mixture (h : Residual_ConditionalMixture) :
    AKLT.Blueprint.Rec.AlphaUniformStatement :=
  main_of_residuals (residuals_of_conditional_mixture h).1
    (residuals_of_conditional_mixture h).2

/-- The removed-mean intervals (blueprint leaf `RemovedMeanIntervalsStatement`),
proved in the copied fiber-expansion development `AKLT.W.REC019.R4`. -/
theorem removedMeanIntervals : AKLT.Blueprint.Rec.RemovedMeanIntervalsStatement :=
  AKLT.W.REC019.R4.main

/-- The triple residual holds: it is the lower interval `41/50 ≤ I` at the pinned choice. -/
theorem residual_tripleLower : Residual_TripleLower := by
  intro a hU f g hN hof hog hfg
  obtain ⟨hb, -, -⟩ := removedMeanIntervals a hU f g hN hof hog hfg
  have h := (hb true).1
  unfold responseI at h
  linarith

/-- The pair residual holds: it is the upper interval `J ≤ 134/125`. -/
theorem residual_pairUpper : Residual_PairUpper := by
  intro a hU f g hN hof hog hfg b
  obtain ⟨hb, -, -⟩ := removedMeanIntervals a hU f g hN hof hog hfg
  have h := (hb b).2.2.2
  unfold responseJ at h
  linarith

/-- The frozen target, unconditionally. -/
theorem main : AKLT.Blueprint.Rec.AlphaUniformStatement :=
  main_of_residuals residual_tripleLower residual_pairUpper

end AKLT.W.REC019
