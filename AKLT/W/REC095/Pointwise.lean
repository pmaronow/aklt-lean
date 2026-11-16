import AKLT.W.REC095.Trace
import AKLT.W.REC010.Main
import AKLT.W.REC011.Main
import AKLT.W.REC012.Main
import AKLT.W.REC013.Main
import AKLT.W.REC041.Main
import AKLT.Cert.H2.Words

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Rec

namespace AKLT.W.REC095

/-- The sole remaining local analytic input. This is the shared matcher,
including missing external factors and the one-sided covering-tip condition. -/
def Residual_CoveredRatio : Prop := CoveredRatioStatementV2

private theorem traceCoefficient_list_product {G : Finset Plane} {n : ℕ}
    (D : Network G) (l : List Plane) (hlen : l.length = n + 1) :
    traceCoefficient D l =
      ∏ i : Fin n, departureCoefficient
        ((traceNetwork D (l.take (i.val + 1))).status
          (l.get ⟨i.val, by omega⟩)) := by
  induction n generalizing D l with
  | zero =>
      cases l with
      | nil => simp at hlen
      | cons y ys =>
          cases ys with
          | nil => simp [traceCoefficient]
          | cons z zs => simp at hlen
  | succ n ih =>
      cases l with
      | nil => simp at hlen
      | cons y ys =>
          cases ys with
          | nil => simp at hlen
          | cons o rest =>
              have ht : (o :: rest).length = n + 1 := by
                simp only [List.length_cons] at hlen ⊢
                omega
              change departureCoefficient (D.status y) *
                traceCoefficient (traceStep D y o) (o :: rest) = _
              rw [ih (traceStep D y o) (o :: rest) ht, Fin.prod_univ_succ]
              congr 1

/-- The coefficient is a product of the actual evolving departure laws. -/
theorem traceCoefficient_product {G : Finset Plane} {n : ℕ}
    (D : Network G) (u : Plane) (w : DirectionWord n) :
    traceCoefficient D (wordVertices u w) =
      ∏ i : Fin n, departureCoefficient
        ((prefixNetwork D u w i.val).status (wordVertex u w i.val)) := by
  have hlen : (wordVertices u w).length = n + 1 := by simp [wordVertices]
  rw [traceCoefficient_list_product D (wordVertices u w) hlen]
  apply Finset.prod_congr rfl
  intro i hi
  simp [prefixNetwork, wordVertices]

private theorem passageFactor_ge_one (straight : Bool) :
    (1 : ℝ) ≤ (passageFactor straight : ℝ) := by
  cases straight <;> norm_num [passageFactor, localThreshold]

private theorem latticeFactor_nonneg {n : ℕ} (u : Plane) (incoming : Compass)
    (w : DirectionWord n) (i : Fin n) :
    (0 : ℝ) ≤ ((if wordRevisit u w i then 1 / 5
      else passageFactor (wordStraight incoming w i) / 3 : ℚ) : ℝ) := by
  split_ifs
  · norm_num
  · push_cast
    exact div_nonneg ((by norm_num : (0 : ℝ) ≤ 1).trans
      (passageFactor_ge_one _)) (by norm_num)

/-- All trace/product bookkeeping is proved here. Only the local H1
comparison for a shared covered departure remains an explicit premise. -/
theorem pointwise_of_coveredRatio (hcovered : Residual_CoveredRatio) :
    OnePointPointwiseStatementV2 := by
  intro hH1 G τ D hD u hu incoming _hmiss n w hstop hex
  classical
  let E (i : Fin n) := prefixNetwork D u w i.val
  let y (i : Fin n) := wordVertex u w i.val
  let o (i : Fin n) := wordVertex u w (i.val + 1)
  have hdyn := traceDynamics G D hD u hu (protectedSites G) n w hstop
  let a (i : Fin n) : Departure :=
    ⟨G, τ, E i, y i, o i, hdyn.1 i.val (Nat.le_of_lt i.isLt),
      (hdyn.2 i).1, present_neighbour (hdyn.1 i.val (Nat.le_of_lt i.isLt)).1
        (hdyn.2 i).2⟩
  let exceptional (i : Fin n) : Prop :=
    (E i).status (y i) = .U ∧
      ¬ AKLT.Defs.CoveredDepartureV2 (E i) (y i) (wordIncoming incoming w i) (w i)
  let M (i : Fin n) : ℝ := if exceptional i then 12 / 5 else 1
  let ω (i : Fin n) : ℝ :=
    ((if wordRevisit u w i then 1 / 5
      else passageFactor (wordStraight incoming w i) / 3 : ℚ) : ℝ)
  have hω (i : Fin n) : 0 ≤ ω i := latticeFactor_nonneg u incoming w i
  have hstep (b : Bool) (i : Fin n) :
      (departureCoefficient ((E i).status (y i)) : ℝ) *
        stepRatio (E i) τ b (y i) (o i) ≤ M i * ω i := by
    have hfree : stepRatio (E i) τ false (y i) (o i) ≤ 1 :=
      AKLT.W.REC011.main (a i)
    have hpinned : stepRatio (E i) τ true (y i) (o i) ≤ 12 / 5 :=
      AKLT.W.REC012.main (a i)
    rcases (hdyn.2 i).1.2.2 with hU | hDs
    · have hstatus : (E i).status (y i) = .U := hU.1
      have hrev : wordRevisit u w i = false := by
        apply Bool.eq_false_of_not_eq_true
        intro hr
        exact revisit_status_ne_U D u w i hr hU.1
      have hpf := passageFactor_ge_one (wordStraight incoming w i)
      by_cases hc : AKLT.Defs.CoveredDepartureV2 (E i) (y i)
          (wordIncoming incoming w i) (w i)
      · have hp : stepRatio (E i) τ true (y i) (o i) ≤
            (passageFactor (wordStraight incoming w i) : ℝ) := by
          apply hcovered hH1 (a i) hU.1 (wordIncoming incoming w i) (w i) _ hc
          exact AKLT.Cert.H2.vertex_succ u w i.val i.isLt
        have hr : stepRatio (E i) τ b (y i) (o i) ≤
            (passageFactor (wordStraight incoming w i) : ℝ) := by
          cases b
          · exact hfree.trans hpf
          · exact hp
        have he : ¬ exceptional i := fun he => he.2 hc
        simp only [M, he, ite_false, one_mul, ω, hrev, Bool.false_eq_true,
          ite_false, Rat.cast_div, Rat.cast_ofNat, departureCoefficient,
          hstatus, ite_true]
        norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
        linarith
      · have he : exceptional i := ⟨hU.1, hc⟩
        have hr : stepRatio (E i) τ b (y i) (o i) ≤ 12 / 5 := by
          cases b
          · exact hfree.trans (by norm_num)
          · exact hpinned
        simp only [M, he, ite_true, ω, hrev, Bool.false_eq_true, ite_false,
          Rat.cast_div, Rat.cast_ofNat, departureCoefficient, hstatus]
        norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
        linarith
    · have hstatus : (E i).status (y i) = .D := hDs.1
      have htrivial : stepRatio (E i) τ b (y i) (o i) = 1 := by
        cases b
        · exact (AKLT.W.REC013.main (a i) hDs.1).2
        · exact (AKLT.W.REC013.main (a i) hDs.1).1
      have he : ¬ exceptional i := by
        intro he
        have : Status.D = .U := hDs.1.symm.trans he.1
        cases this
      have hpf := passageFactor_ge_one (wordStraight incoming w i)
      simp only [htrivial, mul_one, M, he, ite_false, one_mul, departureCoefficient,
        hstatus, reduceCtorEq, ite_false, ite_true]
      dsimp only [ω]
      split_ifs
      · norm_num
      · push_cast
        linarith
  have hprodM : (∏ i, M i) = (12 / 5 : ℝ) ^ uncoveredCountV2 D u incoming w := by
    dsimp only [M]
    rw [← Finset.prod_filter]
    simp only [Finset.prod_const]
    rfl
  have hprodω : (∏ i, ω i) = (trailWeight u incoming w : ℝ) := by
    simp only [trailWeight, Rat.cast_prod]
    rfl
  have hcount : (12 / 5 : ℝ) ^ uncoveredCountV2 D u incoming w ≤ exceptionFactor := by
    exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 12 / 5) hex
  have hpin (b : Bool) :
      (traceCoefficient D (wordVertices u w) : ℝ) *
        traceRatio D τ b (wordVertices u w) ≤
          exceptionFactor * (trailWeight u incoming w : ℝ) := by
    rw [traceCoefficient_product, Rat.cast_prod,
      AKLT.W.REC041.main G τ D hD u hu (protectedSites G) n w hstop b,
      ← Finset.prod_mul_distrib]
    change (∏ i, (departureCoefficient ((E i).status (y i)) : ℝ) *
      stepRatio (E i) τ b (y i) (o i)) ≤ _
    calc
      _ ≤ ∏ i, M i * ω i := by
        apply Finset.prod_le_prod₀
        · intro i hi
          exact mul_nonneg (by exact_mod_cast departureCoefficient_nonneg _)
            (AKLT.W.REC010.main (a i) b).le
        · intro i hi
          exact hstep b i
      _ = (∏ i, M i) * ∏ i, ω i := Finset.prod_mul_distrib
      _ ≤ exceptionFactor * (∏ i, ω i) :=
        mul_le_mul_of_nonneg_right (by rw [hprodM]; exact hcount)
          (Finset.prod_nonneg fun i _ => hω i)
      _ = _ := by rw [hprodω]
  rcases le_total (traceRatio D τ true (wordVertices u w))
      (traceRatio D τ false (wordVertices u w)) with h | h
  · rw [max_eq_right h]
    exact hpin false
  · rw [max_eq_left h]
    exact hpin true

end AKLT.W.REC095
