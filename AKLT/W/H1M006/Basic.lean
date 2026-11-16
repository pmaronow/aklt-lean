import AKLT.Blueprint.H1.NodesPassage

noncomputable section
open scoped BigOperators
open AKLT.Defs
open AKLT.Blueprint.H1

namespace AKLT.W.H1M006

/-- The active template with the passage site erased. -/
def passageComplement (π : PatternData) : Finset Plane := π.active.erase (0, 0)

/-- The original summand, with the observable set to one. -/
def originalSummand (π : PatternData) (next : Bool) (m : Fin 20 → UnitVector)
    (n : (x : π.active) → SpinLetter) : ℝ :=
  (∏ x : π.active,
    spinWeight (if next ∧ x.val = (0, 0) then .D else π.statusAt x.val) (n x)) *
  (∏ e ∈ π.bonds,
    if next ∧ ({e.1, e.2} : Finset Plane) = {(0, 0), π.outgoing.step} then 1
    else 1 + dot (π.spins n e.1) (π.spins n e.2)) *
  ∏ j : Fin 20,
    if π.statusAt (externalSlot j).1 = .X then 1
    else 1 + dot (m j).val (π.spins n (externalSlot j).1)

/-- One summand of the functional after the passage coordinate is erased. -/
def erasedSummand (π : PatternData) (m : Fin 20 → UnitVector)
    (F : (Plane → Vec3) → ℝ) (n : passageComplement π → SpinLetter) : ℝ :=
  (∏ x : passageComplement π, spinWeight (π.statusAt x.val) (n x)) *
  F (supportSpins (passageComplement π) n) *
  (∏ e ∈ π.bonds,
    if e.1 = (0, 0) ∨ e.2 = (0, 0) then 1
    else 1 + dot (supportSpins (passageComplement π) n e.1)
      (supportSpins (passageComplement π) n e.2)) *
  ∏ j : Fin 20,
    if π.statusAt (externalSlot j).1 = .X then 1
    else 1 + dot (m j).val
      (supportSpins (passageComplement π) n (externalSlot j).1)

/-- Splits a full active spin assignment into the erased assignment and passage atom. -/
def splitAssignments (π : PatternData) (h0 : (0, 0) ∈ π.active) :
    ((passageComplement π → SpinLetter) × SpinLetter) ≃
      ((x : π.active) → SpinLetter) where
  toFun q x := if hx : x.val = (0, 0) then q.2 else
    q.1 ⟨x.val, Finset.mem_erase.mpr ⟨hx, x.property⟩⟩
  invFun n := (fun x => n ⟨x.val, (Finset.mem_erase.mp x.property).2⟩,
    n ⟨(0, 0), h0⟩)
  left_inv q := by
    rcases q with ⟨v, p⟩
    apply Prod.ext
    · funext x
      have hx : x.val ≠ (0, 0) := (Finset.mem_erase.mp x.property).1
      simp only [hx]
      exact congrArg v (Subtype.ext rfl)
    · rfl
  right_inv n := by
    funext x
    by_cases hx : x.val = (0, 0)
    · have hx' : x = ⟨(0, 0), h0⟩ := Subtype.ext hx
      subst x
      simp
    · simp [hx]

theorem origin_mem_template : (0, 0) ∈ templateSites := by
  norm_num [templateSites, square, latticeDist]

theorem origin_active (π : PatternData) (hπ : π.Covered) :
    (0, 0) ∈ π.active := by
  rcases hπ with ⟨_, h0, _⟩
  rw [PatternData.active, Finset.mem_filter]
  constructor
  · exact origin_mem_template
  · rw [h0]
    decide

end AKLT.W.H1M006
