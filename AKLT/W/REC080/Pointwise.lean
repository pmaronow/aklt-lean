import AKLT.W.REC080.SharedCover
import AKLT.W.REC011.Main
import AKLT.W.REC012.Main
import AKLT.W.REC013.Main
import AKLT.W.REC041.Main

noncomputable section
open scoped BigOperators ENNReal
open AKLT.Defs AKLT.Blueprint.Rec

namespace AKLT.W.REC080

theorem passageFactor_ge_one (straight : Bool) : (1 : ℝ) ≤ passageFactor straight := by
  cases straight <;> norm_num [passageFactor, localThreshold]

theorem coefficient_list_product {G : Finset Plane} {n : ℕ} (D : Network G)
    (l : List Plane) (hlen : l.length = n + 1) :
    traceCoefficient D l =
      ∏ i : Fin n,
        if (traceNetwork D (l.take (i.val + 1))).status (l.get ⟨i.val, by omega⟩) = .U
        then (1 / 3 : ℚ)
        else if (traceNetwork D (l.take (i.val + 1))).status (l.get ⟨i.val, by omega⟩) = .D
        then 1 / 5 else 0 := by
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
        have htail : (o :: rest).length = n + 1 := by
          simp only [List.length_cons] at hlen ⊢
          omega
        rw [traceCoefficient, ih (traceStep D y o) (o :: rest) htail]
        simp only [Fin.prod_univ_succ]
        congr 1

theorem coefficient_word_product {G : Finset Plane} {n : ℕ} (D : Network G)
    (u : Plane) (w : DirectionWord n) :
    (traceCoefficient D (wordVertices u w) : ℝ) =
      ∏ i : Fin n,
        if (prefixNetwork D u w i.val).status (wordVertex u w i.val) = .U
        then (1 / 3 : ℝ)
        else if (prefixNetwork D u w i.val).status (wordVertex u w i.val) = .D
        then 1 / 5 else 0 := by
  rw [coefficient_list_product (n := n) D (wordVertices u w) (by simp [wordVertices])]
  push_cast
  apply Finset.prod_congr rfl
  intro i _
  simp only [prefixNetwork, wordVertices, List.get_eq_getElem, List.getElem_map,
    List.getElem_range]
  split_ifs <;> simp_all

theorem u_not_revisit {G : Finset Plane} {n : ℕ} (D : Network G) (u : Plane)
    (w : DirectionWord n) (i : Fin n)
    (hU : (prefixNetwork D u w i.val).status (wordVertex u w i.val) = .U) :
    wordRevisit u w i = false := by
  have hnot := (trace_status_U_iff D ((wordVertices u w).take (i.val + 1))
    (wordVertex u w i.val)).mp hU
  rw [prefix_departures u w i.val (Nat.le_of_lt i.isLt)] at hnot
  have hcount : departureCount u w i.val (wordVertex u w i.val) = 0 := by
    rw [departureCount, Nat.min_eq_left (Nat.le_of_lt i.isLt), Finset.card_eq_zero]
    apply Finset.filter_eq_empty_iff.mpr
    intro j hj hjy
    exact hnot.2 (List.mem_map.mpr ⟨j, List.mem_range.mpr (Finset.mem_range.mp hj), hjy⟩)
  simp [wordRevisit, hcount]

/-- Once the shared local ratio comparison is supplied, all remaining
pointwise estimates use proved ratio bounds and finite products. -/
theorem onePointPointwise_of_coveredRatio (hCovered : CoveredRatioStatementV2) :
    OnePointPointwiseStatementV2 := by
  classical
  intro hH1 G τ D hD u hu incoming _ n w hw hcount
  let E (i : Fin n) := prefixNetwork D u w i.val
  let y (i : Fin n) := wordVertex u w i.val
  let o (i : Fin n) := wordVertex u w (i.val + 1)
  let bad (i : Fin n) : Prop := (E i).status (y i) = .U ∧
    ¬ AKLT.Defs.CoveredDepartureV2 (E i) (y i) (wordIncoming incoming w i) (w i)
  let penalty (i : Fin n) : ℝ := if bad i then 12 / 5 else 1
  let lattice (i : Fin n) : ℝ := if wordRevisit u w i then 1 / 5
    else (passageFactor (wordStraight incoming w i) : ℝ) / 3
  let coeff (i : Fin n) : ℝ := if (E i).status (y i) = .U then 1 / 3
    else if (E i).status (y i) = .D then 1 / 5 else 0
  have hDyn := AKLT.W.REC039.main G D hD u hu (protectedSites G) n w hw
  let dep (i : Fin n) : Departure :=
    ⟨G, τ, E i, y i, o i, hDyn.1 i.val (Nat.le_of_lt i.isLt),
      (hDyn.2 i).1, AKLT.W.REC096.present_mem_neighbours (hDyn.2 i).2⟩
  have hstep (i : Fin n) (b : Bool) :
      coeff i * stepRatio (E i) τ b (y i) (o i) ≤ penalty i * lattice i := by
    have hpass := passageFactor_ge_one (wordStraight incoming w i)
    have hfree := AKLT.W.REC011.main (dep i)
    have hpinned := AKLT.W.REC012.main (dep i)
    rcases (hDyn.2 i).1.2.2 with ⟨hU, _⟩ | ⟨hD', _⟩
    · change (E i).status (y i) = .U at hU
      have hrev : wordRevisit u w i = false := u_not_revisit D u w i hU
      by_cases hcov : AKLT.Defs.CoveredDepartureV2 (E i) (y i)
          (wordIncoming incoming w i) (w i)
      · have hb : ¬ bad i := fun hh => hh.2 hcov
        have hlocal := hCovered hH1 (dep i) hU (wordIncoming incoming w i) (w i)
          (AKLT.W.REC096.word_vertex_succ u w i.val i.isLt) hcov
        change stepRatio (E i) τ true (y i) (o i) ≤
          (passageFactor (wordStraight incoming w i) : ℝ) at hlocal
        change stepRatio (E i) τ false (y i) (o i) ≤ _ at hfree
        change stepRatio (E i) τ true (y i) (o i) ≤ _ at hpinned
        simp only [coeff, hU, ↓reduceIte, penalty, hb, lattice, hrev, Bool.false_eq_true,
          one_mul, ↓reduceIte]
        cases b
        · nlinarith
        · nlinarith
      · have hb : bad i := ⟨hU, hcov⟩
        change stepRatio (E i) τ false (y i) (o i) ≤ _ at hfree
        change stepRatio (E i) τ true (y i) (o i) ≤ _ at hpinned
        simp only [coeff, hU, ↓reduceIte, penalty, hb, lattice, hrev, Bool.false_eq_true,
          ↓reduceIte]
        cases b <;> nlinarith
    · change (E i).status (y i) = .D at hD'
      have hb : ¬ bad i := by
        rintro ⟨hU, _⟩
        have he : Status.D = .U := hD'.symm.trans hU
        cases he
      have hr : stepRatio (E i) τ b (y i) (o i) = 1 := by
        cases b
        · exact (AKLT.W.REC013.main (dep i) hD').2
        · exact (AKLT.W.REC013.main (dep i) hD').1
      simp [coeff, hD', hr, penalty, hb, lattice]
      split_ifs <;> linarith
  have hlattice : ∏ i : Fin n, lattice i = (trailWeight u incoming w : ℝ) := by
    unfold trailWeight
    push_cast
    apply Finset.prod_congr rfl
    intro i _
    dsimp only [lattice]
    split_ifs <;> norm_num
  have hpenalty : ∏ i : Fin n, penalty i = (12 / 5 : ℝ) ^ uncoveredCountV2 D u incoming w := by
    dsimp only [penalty]
    rw [Finset.prod_ite]
    simp only [Finset.prod_const_one, mul_one, Finset.prod_const]
    rfl
  have hbound (b : Bool) :
      (traceCoefficient D (wordVertices u w) : ℝ) * traceRatio D τ b (wordVertices u w) ≤
        exceptionFactor * (trailWeight u incoming w : ℝ) := by
    rw [coefficient_word_product, AKLT.W.REC041.main G τ D hD u hu (protectedSites G) n w hw b,
      ← Finset.prod_mul_distrib]
    calc
      _ ≤ ∏ i : Fin n, penalty i * lattice i := by
        apply Finset.prod_le_prod₀
        · intro i _
          change 0 ≤ coeff i * stepRatio (E i) τ b (y i) (o i)
          exact mul_nonneg (by dsimp only [coeff]; split_ifs <;> norm_num)
            (traceRatio_nonneg (E i) τ b [y i, o i])
        · intro i _
          exact hstep i b
      _ = (12 / 5 : ℝ) ^ uncoveredCountV2 D u incoming w * (trailWeight u incoming w : ℝ) := by
        rw [Finset.prod_mul_distrib, hpenalty, hlattice]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 12 / 5) hcount)
        (trailWeight_nonneg u incoming w)
  rw [mul_max_of_nonneg _ _ (by exact_mod_cast traceCoefficient_nonneg D (wordVertices u w))]
  exact max_le (hbound true) (hbound false)

end AKLT.W.REC080
