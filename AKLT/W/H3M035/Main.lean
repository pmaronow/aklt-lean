import AKLT.Blueprint.H3.NodesV2Quotient

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.H3M035

private theorem stopped_step_pullback {m q : ℕ} (_hm : 1 ≤ m)
    (Q : MemoryQuotient m q) (hQ : Q.Correct)
    (hclose : ∀ w : DirectionWord m, RawWindow w → ∀ d : Compass,
      WindowAdmissible w d → RawWindow (windowSuccessor w d))
    (p : ℕ)
    (weight : Fin p → Fin p → StepKind → Compass → Compass → Plane → ℚ)
    (hweight : ∀ φ ψ d a a' x,
      weight φ ψ .revisit d a x = weight φ ψ .revisit d a' x)
    (terminalRaw : Fin p → DirectionWord m → Plane → Bool)
    (terminalQuotient : Fin p → Fin q → Plane → Bool)
    (hterminal : ∀ φ w, RawWindow w → ∀ x,
      terminalRaw φ w x = terminalQuotient φ (Q.project w) x)
    (F : Fin p → DirectionWord m → Plane → ℚ)
    (G : Fin p → Fin q → Plane → ℚ)
    (hFG : ∀ ψ w, RawWindow w → ∀ y,
      F ψ w y = G ψ (Q.project w) y)
    (φ : Fin p) (w : DirectionWord m) (hw : RawWindow w) (x : Plane) :
    AKLT.Blueprint.H3.rawStoppedBackwardV2 m p weight terminalRaw F φ w x =
      AKLT.Blueprint.H3.quotientStoppedBackwardV2 Q p weight terminalQuotient G
        φ (Q.project w) x := by
  classical
  unfold AKLT.Blueprint.H3.rawStoppedBackwardV2
    AKLT.Blueprint.H3.quotientStoppedBackwardV2
  rw [hterminal φ w hw x]
  cases ht : terminalQuotient φ (Q.project w) x with
  | true => simp
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    apply Finset.sum_congr rfl
    intro d _
    apply Finset.sum_congr rfl
    intro ψ _
    by_cases hd : WindowAdmissible w d
    · rcases (hQ.2 w hw d) with ⟨hallowed, hfields⟩
      have hallowed' : Q.allowed (Q.project w) d = true := hallowed.mpr hd
      rcases hfields hd with ⟨hkind, hsuccessor, harrival⟩
      have hcoeff :
          weight φ ψ (windowKind w d) d (windowArrival w) x =
            weight φ ψ (Q.kind (Q.project w) d) d
              (Q.arrival (Q.project w)) x := by
        calc
          weight φ ψ (windowKind w d) d (windowArrival w) x =
              weight φ ψ (windowKind w d) d (Q.arrival (Q.project w)) x := by
                by_cases hr : windowKind w d = .revisit
                · rw [hr]
                  exact hweight φ ψ d (windowArrival w) (Q.arrival (Q.project w)) x
                · rw [harrival hr]
          _ = weight φ ψ (Q.kind (Q.project w) d) d
                (Q.arrival (Q.project w)) x := by rw [hkind]
      have hchild := hFG ψ (windowSuccessor w d) (hclose w hw d hd)
        (x + d.step)
      simp only [hd, hallowed', ↓reduceIte]
      calc
        weight φ ψ (windowKind w d) d (windowArrival w) x *
            F ψ (windowSuccessor w d) (x + d.step) =
          weight φ ψ (windowKind w d) d (windowArrival w) x *
            G ψ (Q.project (windowSuccessor w d)) (x + d.step) := by rw [hchild]
        _ = weight φ ψ (Q.kind (Q.project w) d) d
              (Q.arrival (Q.project w)) x *
            G ψ (Q.successor (Q.project w) d) (x + d.step) := by
              rw [hcoeff, ← hsuccessor]
    · have hnot : Q.allowed (Q.project w) d ≠ true := by
        intro ha
        exact hd ((hQ.2 w hw d).1.mp ha)
      have hfalse : Q.allowed (Q.project w) d = false := by
        cases ha : Q.allowed (Q.project w) d with
        | false => rfl
        | true => exact (hnot ha).elim
      simp [hd, hfalse]

private theorem stopped_iterate_pullback {m q : ℕ} (hm : 1 ≤ m)
    (Q : MemoryQuotient m q) (hQ : Q.Correct)
    (hclose : ∀ w : DirectionWord m, RawWindow w → ∀ d : Compass,
      WindowAdmissible w d → RawWindow (windowSuccessor w d))
    (p : ℕ)
    (weight : Fin p → Fin p → StepKind → Compass → Compass → Plane → ℚ)
    (hweight : ∀ φ ψ d a a' x,
      weight φ ψ .revisit d a x = weight φ ψ .revisit d a' x)
    (terminalRaw : Fin p → DirectionWord m → Plane → Bool)
    (terminalQuotient : Fin p → Fin q → Plane → Bool)
    (hterminal : ∀ φ w, RawWindow w → ∀ x,
      terminalRaw φ w x = terminalQuotient φ (Q.project w) x)
    (rewardRaw : Fin p → DirectionWord m → Plane → ℚ)
    (rewardQuotient : Fin p → Fin q → Plane → ℚ)
    (hreward : ∀ φ w, RawWindow w → ∀ x,
      rewardRaw φ w x = rewardQuotient φ (Q.project w) x) :
    ∀ n φ w, RawWindow w → ∀ x,
      (((AKLT.Blueprint.H3.rawStoppedBackwardV2 m p weight terminalRaw)^[n])
        rewardRaw) φ w x =
      (((AKLT.Blueprint.H3.quotientStoppedBackwardV2 Q p weight terminalQuotient)^[n])
        rewardQuotient) φ (Q.project w) x := by
  intro n
  induction n with
  | zero =>
      intro φ w hw x
      simpa only [Function.iterate_zero_apply] using hreward φ w hw x
  | succ n ih =>
      intro φ w hw x
      rw [Function.iterate_succ_apply']
      rw [Function.iterate_succ_apply']
      refine stopped_step_pullback hm Q hQ hclose p weight hweight
        terminalRaw terminalQuotient hterminal
        (((AKLT.Blueprint.H3.rawStoppedBackwardV2 m p weight terminalRaw)^[n])
          rewardRaw)
        (((AKLT.Blueprint.H3.quotientStoppedBackwardV2 Q p weight terminalQuotient)^[n])
          rewardQuotient)
        ?_ φ w hw x
      intro ψ w' hw' y
      exact ih ψ w' hw' y

theorem main :
    AKLT.Blueprint.H3.StoppedQuotientIntertwiningStatementV2 := by
  intro m q hm Q hQ hclose p weight hweight terminalRaw terminalQuotient
    hterminal rewardRaw rewardQuotient hreward _hvanish R φ w hw x
  apply Finset.sum_congr rfl
  intro j _
  apply stopped_iterate_pullback hm Q hQ hclose p weight hweight
    terminalRaw terminalQuotient hterminal rewardRaw rewardQuotient hreward
    j φ w hw x

end AKLT.W.H3M035

#print axioms AKLT.W.H3M035.main
