module
public import AKLT.Cert.H1.Production.Leaves

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

namespace AKLT.W.H1C012

open AKLT.Cert.H1 AKLT.Cert.H1.Production

def parityStep {α : Type} (site : α → PackedSite) (bit : α → Bool)
    (par : Nat) (x : α) : Nat :=
  if (site x).spec.nslots == 0 then par else 2*par + (bit x).toNat

private theorem parity_fold_acc {α : Type} (site : α → PackedSite) (bit : α → Bool)
    (xs : List α) (par : Nat) :
    xs.foldl (parityStep site bit) par =
      2^(((xs.map site).filter (fun s => s.spec.nslots != 0)).length) * par +
        xs.foldl (parityStep site bit) 0 := by
  induction xs generalizing par with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.map_cons]
    rw [ih (parityStep site bit par x), ih (parityStep site bit 0 x)]
    by_cases h : (site x).spec.nslots = 0
    · simp [parityStep, h]
    · simp [parityStep, h, Nat.pow_succ]
      ring

/-- Every selection of the available exterior-pair bits occurs in the list.
The value of `bit` at an empty site is immaterial. -/
theorem parity_fold_mem {α : Type} (site : α → PackedSite) (bit : α → Bool)
    (xs : List α)
    (hbit : ∀ x ∈ xs, (site x).spec.nslots ≠ 0 → bit x = true →
      (site x).spec.nslots = 2 ∧ (site x).spec.diluted = true) :
    xs.foldl (parityStep site bit) 0 ∈ exchangeParities (xs.map site) := by
  induction xs with
  | nil => simp [exchangeParities]
  | cons x xs ih =>
    have htail := ih (fun y hy => hbit y (List.mem_cons_of_mem x hy))
    simp only [List.foldl_cons, List.map_cons, exchangeParities]
    by_cases h : (site x).spec.nslots = 0
    · simpa only [h, beq_self_eq_true, ite_true, parityStep] using htail
    · simp only [beq_iff_eq, h, ite_false]
      rw [parity_fold_acc]
      cases hb : bit x with
      | false =>
        simp only [parityStep, beq_iff_eq, h, ite_false, hb, Bool.toNat_false,
          Nat.mul_zero, Nat.add_zero, Nat.zero_add]
        split
        · exact List.mem_append_left _ htail
        · exact htail
      | true =>
        have hx := hbit x (List.mem_cons_self) h hb
        have hs : parityStep site bit 0 x = 1 := by simp [parityStep, h, hb]
        rw [hs, Nat.mul_one]
        simp only [hx.1, beq_self_eq_true, hx.2, Bool.and_true, ite_true]
        exact List.mem_append_right _ (List.mem_map.mpr ⟨_, htail, rfl⟩)

#print axioms parityStep
#print axioms parity_fold_mem

end AKLT.W.H1C012
