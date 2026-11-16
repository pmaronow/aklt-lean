import AKLT.Blueprint.Rec.NodesV2Handoff
import AKLT.Cert.H2.Words

noncomputable section
open scoped BigOperators
open AKLT.Defs
open AKLT.Blueprint.Rec
open AKLT.Cert.H2

namespace AKLT.W.REC102

private theorem stoppedOperator_pullback
    {m q p : ℕ} (Q : MemoryQuotient m q) (hQ : Q.Correct)
    (weight : Fin p → Fin p → StepKind → Compass → Compass → Plane → ℚ)
    (harrival : ∀ φ ψ d a a' x,
      weight φ ψ .revisit d a x = weight φ ψ .revisit d a' x)
    (rawStop : Fin p → DirectionWord m → Plane → Bool)
    (quotientStop : Fin p → Fin q → Plane → Bool)
    (hstop : ∀ φ w, RawWindow w → ∀ x,
      rawStop φ w x = quotientStop φ (Q.project w) x)
    (rawF : Fin p × DirectionWord m × Plane → ℚ)
    (quotientF : Fin p × Fin q × Plane → ℚ)
    (hF : ∀ φ w, RawWindow w → ∀ x,
      rawF (φ, w, x) = quotientF (φ, Q.project w, x))
    (φ : Fin p) (w : DirectionWord m) (hw : RawWindow w) (x : Plane) :
    rawStoppedOperatorV2 weight rawStop rawF (φ, w, x) =
      quotientStoppedOperatorV2 Q weight quotientStop quotientF (φ, Q.project w, x) := by
  classical
  by_cases hs : rawStop φ w x = true
  · have hqs : quotientStop φ (Q.project w) x = true := by
      rw [← hstop φ w hw x]
      exact hs
    simp [rawStoppedOperatorV2, quotientStoppedOperatorV2, hs, hqs]
  · have hqs : quotientStop φ (Q.project w) x ≠ true := by
      intro h
      apply hs
      rw [hstop φ w hw x]
      exact h
    have hallowed (d : Compass) := (hQ.2 w hw d).1
    have hedge (d : Compass) (hd : WindowAdmissible w d) :
        Q.kind (Q.project w) d = windowKind w d ∧
        Q.successor (Q.project w) d = Q.project (windowSuccessor w d) ∧
        (windowKind w d ≠ .revisit → Q.arrival (Q.project w) = windowArrival w) :=
      (hQ.2 w hw d).2 hd
    simp only [rawStoppedOperatorV2, quotientStoppedOperatorV2, hs, hqs,
      Bool.false_eq_true, ite_false]
    apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro ψ hψ
    by_cases hadm : WindowAdmissible w d
    · have hallow : Q.allowed (Q.project w) d = true := (hallowed d).2 hadm
      have he := hedge d hadm
      have hweight :
          weight φ ψ (windowKind w d) d (windowArrival w) x =
            weight φ ψ (Q.kind (Q.project w) d) d (Q.arrival (Q.project w)) x := by
        rw [he.1]
        by_cases hrev : windowKind w d = .revisit
        · rw [hrev]
          exact harrival φ ψ d (windowArrival w) (Q.arrival (Q.project w)) x
        · rw [he.2.2 hrev]
      have hnext :
          rawF (ψ, windowSuccessor w d, x + d.step) =
            quotientF (ψ, Q.successor (Q.project w) d, x + d.step) := by
        rw [he.2.1]
        exact hF ψ (windowSuccessor w d) (successor_raw w d hw hadm) (x + d.step)
      simp [hadm, hallow, hweight, hnext]
    · have hnotallow : Q.allowed (Q.project w) d ≠ true := by
        intro ha
        exact hadm ((hallowed d).1 ha)
      simp [hadm, hnotallow]

private theorem iterates_pullback
    {m q p : ℕ} (Q : MemoryQuotient m q) (hQ : Q.Correct)
    (weight : Fin p → Fin p → StepKind → Compass → Compass → Plane → ℚ)
    (harrival : ∀ φ ψ d a a' x,
      weight φ ψ .revisit d a x = weight φ ψ .revisit d a' x)
    (rawStop : Fin p → DirectionWord m → Plane → Bool)
    (quotientStop : Fin p → Fin q → Plane → Bool)
    (hstop : ∀ φ w, RawWindow w → ∀ x,
      rawStop φ w x = quotientStop φ (Q.project w) x)
    (rawReward : Fin p × DirectionWord m × Plane → ℚ)
    (quotientReward : Fin p × Fin q × Plane → ℚ)
    (hreward : ∀ φ w, RawWindow w → ∀ x,
      rawReward (φ, w, x) = quotientReward (φ, Q.project w, x)) :
    ∀ j φ w, RawWindow w → ∀ x,
      ((rawStoppedOperatorV2 weight rawStop)^[j]) rawReward (φ, w, x) =
        ((quotientStoppedOperatorV2 Q weight quotientStop)^[j]) quotientReward
          (φ, Q.project w, x) := by
  intro j
  induction j with
  | zero =>
      intro φ w hw x
      simpa using hreward φ w hw x
  | succ j ih =>
      intro φ w hw x
      have hraw :
          ((rawStoppedOperatorV2 weight rawStop)^[j + 1]) rawReward =
            rawStoppedOperatorV2 weight rawStop
              (((rawStoppedOperatorV2 weight rawStop)^[j]) rawReward) :=
        congrArg (fun f => f rawReward)
          (Function.iterate_succ' (rawStoppedOperatorV2 weight rawStop) j)
      have hquot :
          ((quotientStoppedOperatorV2 Q weight quotientStop)^[j + 1]) quotientReward =
            quotientStoppedOperatorV2 Q weight quotientStop
              (((quotientStoppedOperatorV2 Q weight quotientStop)^[j]) quotientReward) :=
        congrArg (fun f => f quotientReward)
          (Function.iterate_succ' (quotientStoppedOperatorV2 Q weight quotientStop) j)
      rw [hraw, hquot]
      exact stoppedOperator_pullback Q hQ weight harrival rawStop quotientStop hstop
        _ _ (fun φ' w' hw' x' => ih φ' w' hw' x') φ w hw x

theorem main : AKLT.Blueprint.Rec.StoppedQuotientSumStatementV2 := by
  intro m q p hm Q hQ weight harrival rawStop quotientStop hstop rawReward quotientReward
    hreward R φ w hw x
  unfold finiteOperatorSum
  apply Finset.sum_congr rfl
  intro j hj
  exact iterates_pullback Q hQ weight harrival rawStop quotientStop hstop
    rawReward quotientReward hreward j φ w hw x

end AKLT.W.REC102

#print axioms AKLT.W.REC102.main
