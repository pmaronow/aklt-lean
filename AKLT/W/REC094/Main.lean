import AKLT.W.REC094.LocalBounds
import AKLT.W.REC090.Main

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC094

def stepCoeff {G : Finset Plane} {n : ℕ} (D : Network G) (u : Plane)
    (w : DirectionWord n) (i : Fin n) : ℝ :=
  let P := AKLT.Blueprint.Rec.prefixNetwork D u w i.val
  if P.status (wordVertex u w i.val) = .U then 1 / 3
  else if P.status (wordVertex u w i.val) = .D then 1 / 5 else 0

def stepWeight {n : ℕ} (u : Plane) (incoming : Compass)
    (w : DirectionWord n) (i : Fin n) : ℝ :=
  if wordRevisit u w i then 1 / 5
  else (passageFactor (wordStraight incoming w i) : ℝ) / 3

def stepException {G : Finset Plane} {n : ℕ} (D : Network G) (u : Plane)
    (incoming : Compass) (w : DirectionWord n) (i : Fin n) : Prop :=
  let P := AKLT.Blueprint.Rec.prefixNetwork D u w i.val
  P.status (wordVertex u w i.val) = .U ∧
    ¬ AKLT.Defs.CoveredDepartureV2 P (wordVertex u w i.val)
      (wordIncoming incoming w i) (w i)

def stepCost {G : Finset Plane} {n : ℕ} (D : Network G) (u : Plane)
    (incoming : Compass) (w : DirectionWord n) (i : Fin n) : ℝ :=
  by classical exact if stepException D u incoming w i then 12 / 5 else 1

/-- Local domination follows from the covered-ratio leaf and proved uniform
bounds. A U departure is a first departure; a D first departure also satisfies
the comparison because 1/5 ≤ passageFactor/3. -/
theorem local_step_comparison (hCovered : AKLT.Blueprint.Rec.CoveredRatioStatementV2)
    (hH1 : AKLT.Blueprint.Top.H1Statement)
    {G : Finset Plane} {n : ℕ} {D : Network G} (τ : PinAssignment G)
    (hD : D.Auxiliary) {u : Plane} (hu : D.AdmissibleStart u)
    (incoming : Compass) {w : DirectionWord n}
    (hTrail : StoppedNetworkTrail D u (protectedSites G) w)
    (i : Fin n) (b : Bool) :
    let P := AKLT.Blueprint.Rec.prefixNetwork D u w i.val
    0 ≤ stepRatio P τ b (wordVertex u w i.val) (wordVertex u w (i.val + 1)) ∧
      stepCoeff D u w i * stepRatio P τ b (wordVertex u w i.val)
        (wordVertex u w (i.val + 1)) ≤
          stepCost D u incoming w i * stepWeight u incoming w i := by
  classical
  let P := AKLT.Blueprint.Rec.prefixNetwork D u w i.val
  let y := wordVertex u w i.val
  let o := wordVertex u w (i.val + 1)
  obtain ⟨haux, hdyn⟩ := trail_dynamics hD hu hTrail
  let a : AKLT.Blueprint.Rec.Departure :=
    ⟨G, τ, P, y, o, haux i.val (Nat.le_of_lt i.isLt),
      (hdyn i).1, present_mem_neighbours (hdyn i).2⟩
  have hp : 1 ≤ (passageFactor (wordStraight incoming w i) : ℝ) :=
    passageFactor_one_le _
  refine ⟨(stepRatio_pos P τ b y o).le, ?_⟩
  change stepCoeff D u w i * stepRatio P τ b y o ≤
    stepCost D u incoming w i * stepWeight u incoming w i
  by_cases hU : P.status y = .U
  · have hfirst := U_departure_first D u w i hU
    have hc : stepCoeff D u w i = 1 / 3 := by simp [stepCoeff, P, y, hU]
    have hw : stepWeight u incoming w i =
        (passageFactor (wordStraight incoming w i) : ℝ) / 3 := by
      simp [stepWeight, hfirst]
    rw [hc, hw]
    by_cases hcov : AKLT.Defs.CoveredDepartureV2 P y (wordIncoming incoming w i) (w i)
    · have hcost : stepCost D u incoming w i = 1 := by
        simp [stepCost, stepException, P, y, hcov]
      have hr : stepRatio P τ b y o ≤
          (passageFactor (wordStraight incoming w i) : ℝ) := by
        cases b with
        | false => exact (AKLT.W.REC011.main a).trans hp
        | true =>
          exact hCovered hH1 a hU (wordIncoming incoming w i) (w i)
            (wordVertex_succ u w i) hcov
      rw [hcost]
      linarith
    · have hcost : stepCost D u incoming w i = 12 / 5 := by
        simp [stepCost, stepException, P, y, hU, hcov]
      have hr : stepRatio P τ b y o ≤ 12 / 5 := stepRatio_le_twelve_fifths a b
      rw [hcost]
      linarith
  · have hDy : P.status y = .D := by
      rcases (hdyn i).1.2.2 with h | h
      · exact False.elim (hU h.1)
      · exact h.1
    have hc : stepCoeff D u w i = 1 / 5 := by
      simp [stepCoeff, P, y, hDy]
    have hcost : stepCost D u incoming w i = 1 := by
      simp [stepCost, stepException, P, y, hU]
    have hr : stepRatio P τ b y o = 1 := dRatio_eq_one a hDy b
    rw [hc, hcost, hr]
    unfold stepWeight
    split_ifs <;> linarith

/-- These identities hold without trail, closure, or admissibility assumptions;
the ratio products telescope using the positive finite partition sums. -/
theorem trace_product_identities {G : Finset Plane} {n : ℕ}
    (D : Network G) (τ : PinAssignment G) (u : Plane) (w : DirectionWord n) :
    (traceCoefficient D (wordVertices u w) : ℝ) = ∏ i : Fin n, stepCoeff D u w i ∧
    traceRatio D τ true (wordVertices u w) =
      ∏ i : Fin n, stepRatio (AKLT.Blueprint.Rec.prefixNetwork D u w i.val) τ true
        (wordVertex u w i.val) (wordVertex u w (i.val + 1)) ∧
    traceRatio D τ false (wordVertices u w) =
      ∏ i : Fin n, stepRatio (AKLT.Blueprint.Rec.prefixNetwork D u w i.val) τ false
        (wordVertex u w i.val) (wordVertex u w (i.val + 1)) := by
  refine ⟨?_, traceRatio_product D τ true u w, traceRatio_product D τ false u w⟩
  rw [traceCoefficient_product, Rat.cast_prod]
  apply Finset.prod_congr rfl
  intro i _
  dsimp [departureCoefficient, stepCoeff]
  split_ifs <;> norm_num

private theorem product_indicator_pow {ι : Type*} (s : Finset ι)
    (p : ι → Prop) [DecidablePred p] (c : ℝ) :
    ∏ i ∈ s, (if p i then c else 1) = c ^ (s.filter p).card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      by_cases hp : p a <;>
        simp [ha, hp, ih, Finset.filter_insert, pow_succ, mul_comm]

/-- Multiply the local comparisons for both pin choices, telescope the ratios,
and pay at most twelve factors of 12/5 before taking their common maximum. -/
theorem main_of_coveredRatio (hCovered : AKLT.Blueprint.Rec.CoveredRatioStatementV2) :
    AKLT.Blueprint.Rec.OnePointPointwiseStatementV2 := by
  intro hH1 G τ D hD u hu incoming hIncoming n w hTrail hCount
  have hLocal := local_step_comparison hCovered hH1 τ hD hu incoming hTrail
  let c : Fin n → ℝ := stepCoeff D u w
  let v : Fin n → ℝ := stepWeight u incoming w
  let e : Fin n → ℝ := stepCost D u incoming w
  let rT : Fin n → ℝ := fun i =>
    stepRatio (AKLT.Blueprint.Rec.prefixNetwork D u w i.val) τ true
      (wordVertex u w i.val) (wordVertex u w (i.val + 1))
  let rF : Fin n → ℝ := fun i =>
    stepRatio (AKLT.Blueprint.Rec.prefixNetwork D u w i.val) τ false
      (wordVertex u w i.val) (wordVertex u w (i.val + 1))
  have hlocalT : ∀ i ∈ Finset.univ, c i * rT i ≤ e i * v i := by
    intro i hi
    exact (hLocal i true).2
  have hlocalF : ∀ i ∈ Finset.univ, c i * rF i ≤ e i * v i := by
    intro i hi
    exact (hLocal i false).2
  have hnonnegT : ∀ i ∈ Finset.univ, 0 ≤ c i * rT i := by
    intro i hi
    exact mul_nonneg (by
      dsimp [c, stepCoeff]
      split_ifs <;> norm_num) ((hLocal i true).1)
  have hnonnegF : ∀ i ∈ Finset.univ, 0 ≤ c i * rF i := by
    intro i hi
    exact mul_nonneg (by
      dsimp [c, stepCoeff]
      split_ifs <;> norm_num) ((hLocal i false).1)
  have hnonnegR : ∀ i ∈ Finset.univ, 0 ≤ e i * v i := by
    intro i hi
    have hp : 0 < (passageFactor (wordStraight incoming w i) : ℝ) := by
      cases wordStraight incoming w i <;>
        norm_num [passageFactor, localThreshold]
    dsimp [e, v, stepCost, stepWeight]
    split_ifs <;> positivity
  have hpT : ∏ i : Fin n, c i * rT i ≤ ∏ i : Fin n, e i * v i :=
    Finset.prod_le_prod₀ hnonnegT hlocalT
  have hpF : ∏ i : Fin n, c i * rF i ≤ ∏ i : Fin n, e i * v i :=
    Finset.prod_le_prod₀ hnonnegF hlocalF
  have hids := trace_product_identities D τ u w
  have hT : (traceCoefficient D (wordVertices u w) : ℝ) *
        traceRatio D τ true (wordVertices u w) ≤ ∏ i : Fin n, e i * v i := by
    rw [hids.1, hids.2.1]
    calc
      (∏ i : Fin n, c i) * (∏ i : Fin n, rT i) = ∏ i : Fin n, c i * rT i := by
        rw [← Finset.prod_mul_distrib]
      _ ≤ ∏ i : Fin n, e i * v i := hpT
  have hF : (traceCoefficient D (wordVertices u w) : ℝ) *
        traceRatio D τ false (wordVertices u w) ≤ ∏ i : Fin n, e i * v i := by
    rw [hids.1, hids.2.2]
    calc
      (∏ i : Fin n, c i) * (∏ i : Fin n, rF i) = ∏ i : Fin n, c i * rF i := by
        rw [← Finset.prod_mul_distrib]
      _ ≤ ∏ i : Fin n, e i * v i := hpF
  have hcoef : 0 ≤ (traceCoefficient D (wordVertices u w) : ℝ) := by
    rw [hids.1]
    apply Finset.prod_nonneg
    intro i hi
    dsimp [c, stepCoeff]
    split_ifs <;> norm_num
  have hmax : (traceCoefficient D (wordVertices u w) : ℝ) *
        max (traceRatio D τ true (wordVertices u w))
          (traceRatio D τ false (wordVertices u w)) ≤ ∏ i : Fin n, e i * v i := by
    calc
      _ = max ((traceCoefficient D (wordVertices u w) : ℝ) *
          traceRatio D τ true (wordVertices u w))
          ((traceCoefficient D (wordVertices u w) : ℝ) *
          traceRatio D τ false (wordVertices u w)) := by
            rw [mul_max_of_nonneg _ _ hcoef]
      _ ≤ ∏ i : Fin n, e i * v i := max_le hT hF
  have hcost : ∏ i : Fin n, e i =
      (12 / 5 : ℝ) ^ AKLT.Blueprint.Rec.uncoveredCountV2 D u incoming w := by
    dsimp [e, stepCost]
    rw [product_indicator_pow]
    congr 1
    unfold AKLT.Blueprint.Rec.uncoveredCountV2
    congr 1
    ext i
    simp [stepException]
  have hweight : ∏ i : Fin n, v i = (trailWeight u incoming w : ℝ) := by
    dsimp [v, stepWeight, trailWeight]
    rw [Rat.cast_prod]
    apply Finset.prod_congr rfl
    intro i hi
    by_cases hr : wordRevisit u w i = true <;>
      simp [hr, Rat.cast_div, Rat.cast_ofNat]
  have hprod : ∏ i : Fin n, e i * v i =
      (12 / 5 : ℝ) ^ AKLT.Blueprint.Rec.uncoveredCountV2 D u incoming w *
        (trailWeight u incoming w : ℝ) := by
    rw [Finset.prod_mul_distrib, hcost, hweight]
  rw [hprod] at hmax
  have hbase : (1 : ℝ) ≤ 12 / 5 := by norm_num
  have hpower : (12 / 5 : ℝ) ^ AKLT.Blueprint.Rec.uncoveredCountV2 D u incoming w ≤
      (12 / 5 : ℝ) ^ 12 := pow_le_pow_right₀ hbase hCount
  have htrailnonneg : 0 ≤ (trailWeight u incoming w : ℝ) := by
    rw [← hweight]
    exact Finset.prod_nonneg (by
      intro i hi
      dsimp [v, stepWeight]
      split_ifs
      · norm_num
      · cases wordStraight incoming w i <;>
          norm_num [passageFactor, localThreshold])
  calc
    (traceCoefficient D (wordVertices u w) : ℝ) *
        max (traceRatio D τ true (wordVertices u w))
          (traceRatio D τ false (wordVertices u w)) ≤
      (12 / 5 : ℝ) ^ AKLT.Blueprint.Rec.uncoveredCountV2 D u incoming w *
        (trailWeight u incoming w : ℝ) := hmax
    _ ≤ (12 / 5 : ℝ) ^ 12 * (trailWeight u incoming w : ℝ) :=
      mul_le_mul_of_nonneg_right hpower htrailnonneg
    _ = AKLT.Blueprint.Rec.exceptionFactor * (trailWeight u incoming w : ℝ) := by
      simp [AKLT.Blueprint.Rec.exceptionFactor]

/-- The covered-ratio comparison is supplied by the proved leaf REC090. -/
theorem main : AKLT.Blueprint.Rec.OnePointPointwiseStatementV2 :=
  main_of_coveredRatio AKLT.W.REC090.main

/-- The exact shared-mixture statement also suffices. -/
theorem main_of_mixture (hMix : AKLT.Blueprint.Rec.LocalMixtureStatementV2) :
    AKLT.Blueprint.Rec.OnePointPointwiseStatementV2 :=
  main_of_coveredRatio (coveredRatio_of_mixture hMix)

#print axioms local_step_comparison
#print axioms trace_product_identities
#print axioms main_of_coveredRatio
#print axioms main
#print axioms main_of_mixture

end AKLT.W.REC094
