module
public import AKLT.W.H1M006.Basic

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.H1

namespace AKLT.W.H1M006

theorem split_spins (π : PatternData) (h0 : (0, 0) ∈ π.active)
    (n : passageComplement π → SpinLetter) (p : SpinLetter) (x : Plane) :
    π.spins (splitAssignments π h0 (n, p)) x =
      if x = (0, 0) then spinVector p else supportSpins (passageComplement π) n x := by
  by_cases hx : x = (0, 0)
  · subst x
    simp [PatternData.spins, splitAssignments, h0]
  · by_cases ha : x ∈ π.active
    · have hc : x ∈ passageComplement π := Finset.mem_erase.mpr ⟨hx, ha⟩
      simp [PatternData.spins, splitAssignments, supportSpins, hx, ha, hc]
    · have hc : x ∉ passageComplement π := fun h => ha (Finset.mem_erase.mp h).2
      simp [PatternData.spins, supportSpins, hx, ha, hc]

theorem prod_subtype_erase (V : Finset Plane) (a : Plane) (ha : a ∈ V)
    (f : V → ℝ) :
    (∏ x : V, f x) = f ⟨a, ha⟩ *
      ∏ x : V.erase a, f ⟨x.val, (Finset.mem_erase.mp x.property).2⟩ := by
  classical
  let g : Plane → ℝ := fun x => if hx : x ∈ V then f ⟨x, hx⟩ else 1
  calc
    _ = ∏ x : V, g x := by
      apply Finset.prod_congr rfl
      intro x _
      simp [g]
    _ = ∏ x ∈ V, g x := Finset.prod_coe_sort V g
    _ = g a * ∏ x ∈ V.erase a, g x := (Finset.mul_prod_erase V g ha).symm
    _ = _ := by
      rw [← Finset.prod_coe_sort]
      simp only [g, dite_eq_left ha]
      congr 1
      apply Finset.prod_congr rfl
      intro x _
      simp [(Finset.mem_erase.mp x.property).2]

theorem split_weights (π : PatternData) (hπ : π.Covered)
    (next : Bool) (n : passageComplement π → SpinLetter) (p : SpinLetter) :
    (∏ x : π.active, spinWeight
      (if next ∧ x.val = (0, 0) then .D else π.statusAt x.val)
      ((splitAssignments π (origin_active π hπ) (n, p)) x)) =
    spinWeight (if next then .D else .U) p *
      ∏ x : passageComplement π, spinWeight (π.statusAt x.val) (n x) := by
  rw [prod_subtype_erase π.active (0, 0) (origin_active π hπ)]
  have h0 := hπ.2.1
  simp only [splitAssignments, Equiv.coe_fn_mk, ↓reduceDIte, and_true, h0]
  congr 1
  apply Finset.prod_congr rfl
  intro x _
  have hx : x.val ≠ (0, 0) := (Finset.mem_erase.mp x.property).1
  simp only [hx, and_false, ↓reduceIte, ↓reduceDIte]
  congr 1

end AKLT.W.H1M006
