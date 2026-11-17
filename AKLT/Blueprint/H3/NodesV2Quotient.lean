module
public import AKLT.Blueprint.H3.NodesAutomaton
public import AKLT.Blueprint.Top.ComputationV2

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.Blueprint.H3

/-- A raw stopped operator allowing terminal tests to inspect the full displayed state.
The terminal test is deliberately separate from its quotient counterpart. -/
def rawStoppedBackwardV2 (m p : ℕ)
    (weight : Fin p → Fin p → StepKind → Compass → Compass → Plane → ℚ)
    (terminal : Fin p → DirectionWord m → Plane → Bool)
    (F : Fin p → DirectionWord m → Plane → ℚ)
    (φ : Fin p) (w : DirectionWord m) (x : Plane) : ℚ := by
  classical
  exact if terminal φ w x then 0 else ∑ d : Compass, ∑ ψ : Fin p,
    if WindowAdmissible w d then weight φ ψ (windowKind w d) d (windowArrival w) x *
      F ψ (windowSuccessor w d) (x + d.step) else 0

/-- Matching quotient stopped operator. Absolute directions retain their multiplicities. -/
def quotientStoppedBackwardV2 {m q : ℕ} (Q : MemoryQuotient m q) (p : ℕ)
    (weight : Fin p → Fin p → StepKind → Compass → Compass → Plane → ℚ)
    (terminal : Fin p → Fin q → Plane → Bool)
    (F : Fin p → Fin q → Plane → ℚ)
    (φ : Fin p) (a : Fin q) (x : Plane) : ℚ :=
  if terminal φ a x then 0 else ∑ d : Compass, ∑ ψ : Fin p,
    if Q.allowed a d then weight φ ψ (Q.kind a d) d (Q.arrival a) x *
      F ψ (Q.successor a d) (x + d.step) else 0

/-- `l:automaton-quotient`, REF2_6 finding 3 (Appendix C lines 315–363).
The raw terminal test AND raw reward must descend to the quotient; the quotient reward
vanishes off its stopping set. The explicit raw-successor premise is supplied by the frozen
closure leaf. Prove one-step rational pullback and induct on iterates; finite summation gives
the result, including the zero-step reward. Gen.Bellman.Automaton.stopped_pullback is the
existing nonnegative generic model. This is an open leaf, including its easy base case. -/
def StoppedQuotientIntertwiningStatementV2 : Prop :=
  ∀ m q : ℕ, 1 ≤ m → ∀ Q : MemoryQuotient m q, Q.Correct →
    (∀ w : DirectionWord m, RawWindow w → ∀ d : Compass,
      WindowAdmissible w d → RawWindow (windowSuccessor w d)) →
    ∀ p : ℕ, ∀ weight : Fin p → Fin p → StepKind → Compass → Compass → Plane → ℚ,
      (∀ φ ψ d a a' x, weight φ ψ .revisit d a x = weight φ ψ .revisit d a' x) →
      ∀ terminalRaw : Fin p → DirectionWord m → Plane → Bool,
      ∀ terminalQuotient : Fin p → Fin q → Plane → Bool,
      (∀ φ w, RawWindow w → ∀ x, terminalRaw φ w x = terminalQuotient φ (Q.project w) x) →
      ∀ rewardRaw : Fin p → DirectionWord m → Plane → ℚ,
      ∀ rewardQuotient : Fin p → Fin q → Plane → ℚ,
      (∀ φ w, RawWindow w → ∀ x, rewardRaw φ w x = rewardQuotient φ (Q.project w) x) →
      (∀ φ a x, terminalQuotient φ a x = false → rewardQuotient φ a x = 0) →
      ∀ R : ℕ, ∀ φ : Fin p, ∀ w : DirectionWord m, RawWindow w → ∀ x : Plane,
        (∑ j ∈ Finset.range (R + 1),
          ((rawStoppedBackwardV2 m p weight terminalRaw)^[j]) rewardRaw φ w x) =
        ∑ j ∈ Finset.range (R + 1),
          ((quotientStoppedBackwardV2 Q p weight terminalQuotient)^[j])
            rewardQuotient φ (Q.project w) x

/-- Assembled paper-facing quotient target. The shared Top quotient target already encodes
position-only terminal data as a pullback; the extra clause covers general displayed-state
terminal data with the referee's missing hypotheses stated explicitly. This is not a leaf. -/
def AutomatonQuotientPaperStatementV2 : Prop :=
  AKLT.Blueprint.Top.AutomatonQuotientStatement ∧
    ∀ m q : ℕ, 1 ≤ m → ∀ Q : MemoryQuotient m q, Q.Correct →
      ∀ p : ℕ, ∀ weight : Fin p → Fin p → StepKind → Compass → Compass → Plane → ℚ,
        (∀ φ ψ d a a' x, weight φ ψ .revisit d a x = weight φ ψ .revisit d a' x) →
        ∀ terminalRaw : Fin p → DirectionWord m → Plane → Bool,
        ∀ terminalQuotient : Fin p → Fin q → Plane → Bool,
        (∀ φ w, RawWindow w → ∀ x, terminalRaw φ w x = terminalQuotient φ (Q.project w) x) →
        ∀ rewardRaw : Fin p → DirectionWord m → Plane → ℚ,
        ∀ rewardQuotient : Fin p → Fin q → Plane → ℚ,
        (∀ φ w, RawWindow w → ∀ x, rewardRaw φ w x = rewardQuotient φ (Q.project w) x) →
        (∀ φ a x, terminalQuotient φ a x = false → rewardQuotient φ a x = 0) →
        ∀ R : ℕ, ∀ φ : Fin p, ∀ w : DirectionWord m, RawWindow w → ∀ x : Plane,
          (∑ j ∈ Finset.range (R + 1),
            ((rawStoppedBackwardV2 m p weight terminalRaw)^[j]) rewardRaw φ w x) =
          ∑ j ∈ Finset.range (R + 1),
            ((quotientStoppedBackwardV2 Q p weight terminalQuotient)^[j])
              rewardQuotient φ (Q.project w) x

end AKLT.Blueprint.H3
