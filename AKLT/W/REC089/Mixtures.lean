module
public import AKLT.W.REC089.Template

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC089

/-- Data for a conditional local mixture, indexed by a finite outside-spin
configuration type. -/
structure ConditionalFamily (Ω : Type) [Fintype Ω]
    (current next : Ω → ℝ) (incoming outgoing : Compass) where
  length : Ω → ℕ
  pattern : (ω : Ω) → Fin (length ω) → PatternData
  slot : (ω : Ω) → Fin (length ω) → (Fin 20 → UnitVector)
  coefficient : (ω : Ω) → Fin (length ω) → ℝ
  admissible : ∀ ω i,
    0 ≤ coefficient ω i ∧ (pattern ω i).Covered ∧
      ((pattern ω i).outgoing = .north ↔ outgoing = incoming)
  current_eq : ∀ ω, current ω =
    ∑ i, coefficient ω i * patternCurrent (pattern ω i) (slot ω i)
  next_eq : ∀ ω, next ω =
    ∑ i, coefficient ω i * patternNext (pattern ω i) (slot ω i)

theorem flattenConditionalFamily {Ω : Type} [Fintype Ω]
    {current next : Ω → ℝ} {incoming outgoing : Compass}
    (F : ConditionalFamily Ω current next incoming outgoing)
    (mass : Ω → ℝ) (hmass : ∀ ω, 0 ≤ mass ω) :
    ∃ k : ℕ, ∃ π : Fin k → PatternData,
      ∃ m : Fin k → (Fin 20 → UnitVector), ∃ weight : Fin k → ℝ,
      (∀ i, 0 ≤ weight i ∧ (π i).Covered ∧
        ((π i).outgoing = .north ↔ outgoing = incoming)) ∧
      (∑ ω, mass ω * current ω) = ∑ i, weight i * patternCurrent (π i) (m i) ∧
      (∑ ω, mass ω * next ω) = ∑ i, weight i * patternNext (π i) (m i) := by
  classical
  let I := Σ ω : Ω, Fin (F.length ω)
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  refine ⟨Fintype.card I, (fun i => F.pattern (e.symm i).1 (e.symm i).2),
    (fun i => F.slot (e.symm i).1 (e.symm i).2),
    (fun i => mass (e.symm i).1 * F.coefficient (e.symm i).1 (e.symm i).2), ?_, ?_, ?_⟩
  · intro i
    let x := e.symm i
    have h := F.admissible x.1 x.2
    exact ⟨mul_nonneg (hmass x.1) h.1, h.2.1, h.2.2⟩
  · calc
      (∑ ω, mass ω * current ω) =
          ∑ ω, mass ω * (∑ j, F.coefficient ω j *
            patternCurrent (F.pattern ω j) (F.slot ω j)) := by
              apply Finset.sum_congr rfl
              intro ω _
              rw [F.current_eq ω]
      _ = ∑ x : I, mass x.1 * F.coefficient x.1 x.2 *
            patternCurrent (F.pattern x.1 x.2) (F.slot x.1 x.2) := by
              simp only [I, Fintype.sum_sigma]
              apply Finset.sum_congr rfl
              intro ω _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j _
              ring
      _ = ∑ i : Fin (Fintype.card I),
            (mass (e.symm i).1 * F.coefficient (e.symm i).1 (e.symm i).2) *
              patternCurrent (F.pattern (e.symm i).1 (e.symm i).2)
                (F.slot (e.symm i).1 (e.symm i).2) := by
              exact (e.symm.sum_comp (fun x : I => mass x.1 * F.coefficient x.1 x.2 *
                patternCurrent (F.pattern x.1 x.2) (F.slot x.1 x.2))).symm
  · calc
      (∑ ω, mass ω * next ω) =
          ∑ ω, mass ω * (∑ j, F.coefficient ω j *
            patternNext (F.pattern ω j) (F.slot ω j)) := by
              apply Finset.sum_congr rfl
              intro ω _
              rw [F.next_eq ω]
      _ = ∑ x : I, mass x.1 * F.coefficient x.1 x.2 *
            patternNext (F.pattern x.1 x.2) (F.slot x.1 x.2) := by
              simp only [I, Fintype.sum_sigma]
              apply Finset.sum_congr rfl
              intro ω _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j _
              ring
      _ = ∑ i : Fin (Fintype.card I),
            (mass (e.symm i).1 * F.coefficient (e.symm i).1 (e.symm i).2) *
              patternNext (F.pattern (e.symm i).1 (e.symm i).2)
                (F.slot (e.symm i).1 (e.symm i).2) := by
              exact (e.symm.sum_comp (fun x : I => mass x.1 * F.coefficient x.1 x.2 *
                patternNext (F.pattern x.1 x.2) (F.slot x.1 x.2))).symm


/-- Convert any finite family of ball-slot templates to unit-slot templates. -/
theorem ballPatternFamily {Ω : Type} [Fintype Ω] (π : PatternData) (hπ : π.Covered)
    (incoming outgoing : Compass) (hstraight : π.outgoing = .north ↔ outgoing = incoming)
    (b : Ω → Fin 20 → Vec3) (hb : ∀ ω j, normSq (b ω j) ≤ 1) :
    Nonempty (ConditionalFamily Ω (fun ω => ballPatternFunctional π false (b ω))
      (fun ω => ballPatternFunctional π true (b ω)) incoming outgoing) := by
  classical
  choose m w hw hsum he using fun ω => pattern_slots_mixture π (b ω) (hb ω)
  let I := Fin 20 → Bool
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  have heq (ω : Ω) (next : Bool) : ballPatternFunctional π next (b ω) =
      ∑ i : Fin (Fintype.card I), w ω (e.symm i) *
        patternFunctional π next (m ω (e.symm i)) (fun _ => 1) := by
    rw [he ω next]
    exact (e.symm.sum_comp (fun q => w ω q *
      patternFunctional π next (m ω q) (fun _ => 1))).symm
  exact ⟨{
    length := fun _ => Fintype.card I
    pattern := fun _ _ => π
    slot := fun ω i => m ω (e.symm i)
    coefficient := fun ω i => w ω (e.symm i)
    admissible := fun ω i => ⟨hw ω (e.symm i), hπ, hstraight⟩
    current_eq := fun ω => heq ω false
    next_eq := fun ω => heq ω true }⟩

#print axioms flattenConditionalFamily
#print axioms ballPatternFamily

end AKLT.W.REC089
