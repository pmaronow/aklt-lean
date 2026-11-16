import AKLT.Blueprint.Rec.NodesV2Ordering

/-! A precise Appendix C handoff for REF2_6 finding 3. This is an open
transfer obligation, not a numerical input or a claim of a passing certificate. -/

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.Blueprint.Rec

/-- The raw stopped operator permits a raw-state terminal indicator,
so its descent cannot be silently inferred just from Q.Correct. -/
def rawStoppedOperatorV2 {m p : ℕ}
    (weight : Fin p → Fin p → StepKind → Compass → Compass → Plane → ℚ)
    (stop : Fin p → DirectionWord m → Plane → Bool)
    (F : Fin p × DirectionWord m × Plane → ℚ)
    (s : Fin p × DirectionWord m × Plane) : ℚ := by
  classical
  exact if stop s.1 s.2.1 s.2.2 then 0 else
    ∑ d : Compass, ∑ ψ : Fin p, if WindowAdmissible s.2.1 d then
      weight s.1 ψ (windowKind s.2.1 d) d (windowArrival s.2.1) s.2.2 *
        F (ψ, windowSuccessor s.2.1 d, s.2.2 + d.step) else 0

/-- The quotient operator uses its own terminal data. Equality with raw
finite stopped sums needs explicit pullback hypotheses for both data sets. -/
def quotientStoppedOperatorV2 {m q p : ℕ} (Q : MemoryQuotient m q)
    (weight : Fin p → Fin p → StepKind → Compass → Compass → Plane → ℚ)
    (stop : Fin p → Fin q → Plane → Bool)
    (F : Fin p × Fin q × Plane → ℚ) (s : Fin p × Fin q × Plane) : ℚ :=
  if stop s.1 s.2.1 s.2.2 then 0 else
    ∑ d : Compass, ∑ ψ : Fin p, if Q.allowed s.2.1 d then
      weight s.1 ψ (Q.kind s.2.1 d) d (Q.arrival s.2.1) s.2.2 *
        F (ψ, Q.successor s.2.1 d, s.2.2 + d.step) else 0

/-- `l:automaton-quotient`, Appendix C lines 315–363; REF2_6 finding 3.
Finite stopped sums intertwine only when BOTH the raw terminal indicator and
terminal reward are pullbacks. Revisit weights are independent of arrival.
This auxiliary handoff is for BP_H3M; Rec consumes the semantic H3 contract
and does not assume this lemma or any numerical certificate automatically. -/
def StoppedQuotientSumStatementV2 : Prop :=
  ∀ m q p : ℕ, 1 ≤ m → ∀ Q : MemoryQuotient m q, Q.Correct →
    ∀ weight : Fin p → Fin p → StepKind → Compass → Compass → Plane → ℚ,
      (∀ φ ψ d a a' x, weight φ ψ .revisit d a x = weight φ ψ .revisit d a' x) →
    ∀ rawStop : Fin p → DirectionWord m → Plane → Bool,
    ∀ quotientStop : Fin p → Fin q → Plane → Bool,
      (∀ φ w, RawWindow w → ∀ x,
        rawStop φ w x = quotientStop φ (Q.project w) x) →
    ∀ rawReward : Fin p × DirectionWord m × Plane → ℚ,
    ∀ quotientReward : Fin p × Fin q × Plane → ℚ,
      (∀ φ w, RawWindow w → ∀ x,
        rawReward (φ, w, x) = quotientReward (φ, Q.project w, x)) →
    ∀ R : ℕ, ∀ φ : Fin p, ∀ w : DirectionWord m, RawWindow w → ∀ x : Plane,
      finiteOperatorSum (rawStoppedOperatorV2 weight rawStop) rawReward R (φ, w, x) =
        finiteOperatorSum (quotientStoppedOperatorV2 Q weight quotientStop)
          quotientReward R (φ, Q.project w, x)

end AKLT.Blueprint.Rec
