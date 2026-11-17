import AKLT.Blueprint.Mom.NodesMean

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.Blueprint.Mom

/-- The optional zero atom for an arbitrary weighted frame law. -/
def frameAtom {k : ℕ} (F : FrameData k) : Option (Fin k) → Vec3
  | none => 0
  | some i => F.point i

/-- The optional zero mass, with the same active-status convention as Top.Exact. -/
def frameWeight {k : ℕ} (F : FrameData k) (s : Status) : Option (Fin k) → ℝ
  | none => if s = .D then 2 / 5 else 0
  | some i => (if s = .D then 3 / 5 else 1) * F.weight i

/-- `l:exact`, lines 317–325: apply the supplied single-site polynomial law
to `prod_i X_i^(m_i)`. Its total degree is at most `sum_i m_i`; the zero atom
changes only positive-degree moments. Repeated frame atoms are allowed. -/
def SingleSiteQuadratureStatement : Prop :=
  ∀ k : ℕ, ∀ F : FrameData k, MomentLaw F →
    ∀ s : Status, s = .U ∨ s = .D →
    ∀ m : Fin 3 → ℕ, (∑ i, m i) ≤ 4 →
      momentLawFunctional F s (mono m) = siteFunctional s (mono m)

/-- `l:exact`, lines 321–325: unpack the Option alphabet used in the Top
statement; it gives exactly the zero-atom mixture, with no normalization quotient. -/
def FrameOptionSumStatement : Prop :=
  ∀ k : ℕ, ∀ F : FrameData k, ∀ s : Status, s = .U ∨ s = .D →
    ∀ f : Vec3 → ℝ,
      finiteFunctional (frameWeight F s) (frameAtom F) f = momentLawFunctional F s f

theorem frameOptionSum : FrameOptionSumStatement := by
  intro k F s hs f
  rcases hs with rfl | rfl
  · simp [finiteFunctional, Fintype.sum_option, frameWeight, frameAtom,
      momentLawFunctional]
  · simp [finiteFunctional, Fintype.sum_option, frameWeight, frameAtom,
      momentLawFunctional, Finset.mul_sum, mul_assoc, add_comm]

/-- A signed pin factor, with arbitrary real coefficient. The paper uses ±1. -/
def pinPolynomial {n : ℕ} (q : (Fin n × Vec3) × ℝ) :
    MvPolynomial (Fin n × Fin 3) ℝ :=
  1 + MvPolynomial.C q.2 *
    ∑ i, MvPolynomial.C (q.1.2 i) * MvPolynomial.X (q.1.1, i)

/-- The complete inserted polynomial, signed bond factors, and signed pins.
Multiplicity is retained in the lists; no factor is silently deduplicated. -/
def interactionPolynomial {n : ℕ} (bonds : List ((Fin n × Fin n) × ℝ))
    (pins : List ((Fin n × Vec3) × ℝ)) (p : MvPolynomial (Fin n × Fin 3) ℝ) :
    MvPolynomial (Fin n × Fin 3) ℝ :=
  p * (bonds.map fun e => 1 + MvPolynomial.C e.2 * dotPolynomial e.1).prod *
    (pins.map pinPolynomial).prod

/-- Occurrences in the interaction factors. Loops contribute two occurrences. -/
def interactionOccurrences {n : ℕ} (bonds : List ((Fin n × Fin n) × ℝ))
    (pins : List ((Fin n × Vec3) × ℝ)) (x : Fin n) : ℕ :=
  (bonds.filter fun e => e.1.1 = x).length +
    (bonds.filter fun e => e.1.2 = x).length +
    (pins.filter fun e => e.1.1 = x).length

/-- `l:exact`, lines 327–331: support degrees add under multiplication;
test the inserted observable together with all factors, counting both endpoints.
The assertion is stronger than the paper's ± signs and unit pins, since those
restrictions play no role in degree control. -/
def InteractionDegreeStatement : Prop :=
  ∀ n : ℕ, ∀ bonds : List ((Fin n × Fin n) × ℝ),
    ∀ pins : List ((Fin n × Vec3) × ℝ), ∀ p : MvPolynomial (Fin n × Fin 3) ℝ,
    (∀ m ∈ p.support, ∀ x : Fin n,
      (∑ i : Fin 3, m (x, i)) + interactionOccurrences bonds pins x ≤ 4) →
      SeparateDegreeFour (interactionPolynomial bonds pins p)

end AKLT.Blueprint.Mom
