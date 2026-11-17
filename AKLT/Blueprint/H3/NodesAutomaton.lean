module
public import AKLT.Blueprint.H3.Basic

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.Blueprint.H3

/-- `l:automaton-quotient`, app-input-contracts.tex:315–354.
Translate a suffix by the first step; injectivity of old bonds restricts to the suffix,
and admissibility separates its new last bond. Memory zero is deliberately excluded. -/
def RawSuccessorStatement : Prop :=
  ∀ m : ℕ, 1 ≤ m → ∀ w : DirectionWord m, RawWindow w →
    ∀ d : Compass, WindowAdmissible w d → RawWindow (windowSuccessor w d)

/-- `l:automaton-quotient`, lines 315–339.
Choose raw representatives using surjectivity, then transport each direction's row and
non-revisit arrival through the fiber hypotheses. No partition-minimizer is trusted. -/
def ProjectionRealizationStatement : Prop :=
  ∀ m q : ℕ, 1 ≤ m → ∀ π : DirectionWord m → Fin q, CompatibleProjection m q π →
    ∃ Q : MemoryQuotient m q, Q.Correct ∧ ∀ w, RawWindow w → Q.project w = π w

/-- Immediate rational counterpart of `Automaton.backward_pullback`.
It needs only the admitted-edge fields of Correct; the iterate argument additionally needs
raw-successor closure. In particular no equality of arrivals on revisit edges is used. -/
theorem rawBackward_pullback {m q : ℕ} (Q : MemoryQuotient m q) (hQ : Q.Correct)
    (p : ℕ) (weight : Fin p → Fin p → StepKind → Compass → Compass → Plane → ℚ)
    (hweight : ∀ φ ψ d a a' x, weight φ ψ .revisit d a x = weight φ ψ .revisit d a' x)
    (terminal : Plane → Bool) (G : Fin p → Fin q → Plane → ℚ)
    (w : DirectionWord m) (hw : RawWindow w) (φ : Fin p) (x : Plane) :
    rawBackward m p weight terminal (fun ψ ω y => G ψ (Q.project ω) y) φ w x =
      quotientBackward Q p weight terminal G φ (Q.project w) x := by
  classical
  unfold rawBackward quotientBackward
  split_ifs with ht
  · rfl
  · apply Finset.sum_congr rfl
    intro d _
    apply Finset.sum_congr rfl
    intro ψ _
    by_cases hd : WindowAdmissible w d
    · obtain ⟨hk, hs, ha⟩ := (hQ.2 w hw d).2 hd
      have hal : Q.allowed (Q.project w) d = true := (hQ.2 w hw d).1.mpr hd
      simp only [hd, hal, ↓reduceIte, hk, hs]
      congr 1
      by_cases hr : windowKind w d = .revisit
      · simpa only [hr] using hweight φ ψ d (windowArrival w) (Q.arrival (Q.project w)) x
      · rw [ha hr]
    · have hal : Q.allowed (Q.project w) d ≠ true :=
        fun hh => hd ((hQ.2 w hw d).1.mp hh)
      simp [hd, hal]

/-- A raw row depends only on its admitted successor values. This preserves the
operator under finite iterates without unfolding the operator inside those iterates. -/
theorem rawBackward_congr {m p : ℕ}
    (weight : Fin p → Fin p → StepKind → Compass → Compass → Plane → ℚ)
    (terminal : Plane → Bool) (F H : Fin p → DirectionWord m → Plane → ℚ)
    (φ : Fin p) (w : DirectionWord m) (x : Plane)
    (h : ∀ ψ d, WindowAdmissible w d →
      F ψ (windowSuccessor w d) (x + d.step) = H ψ (windowSuccessor w d) (x + d.step)) :
    rawBackward m p weight terminal F φ w x = rawBackward m p weight terminal H φ w x := by
  classical
  unfold rawBackward
  split_ifs
  · rfl
  · apply Finset.sum_congr rfl
    intro d _
    apply Finset.sum_congr rfl
    intro ψ _
    split_ifs with hd
    · rw [h ψ d hd]
    · rfl

end AKLT.Blueprint.H3
