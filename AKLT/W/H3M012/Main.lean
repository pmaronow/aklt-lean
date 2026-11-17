module
public import AKLT.Blueprint.H3.NodesDomination

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

namespace AKLT.W.H3M012

open AKLT.Defs

private theorem shifted_filter_count_le {α : Type} [DecidableEq α]
    (f : ℕ → α) (n : ℕ) (z : α) :
    ((Finset.range n).filter fun j => f j = z).card ≤
      ((Finset.range n).filter fun j => f (j + 1) = z).card + 1 := by
  classical
  let departures := (Finset.range n).filter fun j => f j = z
  let positiveDepartures := (Finset.range n).filter fun j => f j = z ∧ 0 < j
  let arrivals := (Finset.range n).filter fun j => f (j + 1) = z
  have hsubset : departures ⊆ positiveDepartures ∪ {0} := by
    intro j hj
    simp only [departures, Finset.mem_filter, Finset.mem_range] at hj
    by_cases hzero : j = 0
    · simp [hzero]
    · apply Finset.mem_union_left
      simp only [positiveDepartures, Finset.mem_filter, Finset.mem_range]
      exact ⟨hj.1, hj.2, Nat.pos_of_ne_zero hzero⟩
  have hinj : Function.Injective (fun j : positiveDepartures =>
      (⟨j.1 - 1, by
        have hj := j.2
        simp only [positiveDepartures, Finset.mem_filter, Finset.mem_range] at hj
        change j.1 - 1 ∈ (Finset.range n).filter (fun k => f (k + 1) = z)
        simp only [Finset.mem_filter, Finset.mem_range]
        constructor
        · omega
        · have heq : (j.1 - 1) + 1 = j.1 := Nat.sub_add_cancel (by omega)
          rw [heq]
          exact hj.2.1⟩ : arrivals)) := by
    intro a b hab
    apply Subtype.ext
    have ha := a.2
    have hb := b.2
    simp only [positiveDepartures, Finset.mem_filter, Finset.mem_range] at ha hb
    have hv := congrArg Subtype.val hab
    dsimp at hv
    omega
  have hcard : positiveDepartures.card ≤ arrivals.card :=
    Finset.card_le_card_of_injective hinj
  calc
    departures.card ≤ (positiveDepartures ∪ {0}).card := Finset.card_le_card hsubset
    _ ≤ positiveDepartures.card + ({0} : Finset ℕ).card := Finset.card_union_le _ _
    _ = positiveDepartures.card + 1 := by simp
    _ ≤ arrivals.card + 1 := Nat.add_le_add_right hcard 1

theorem main : AKLT.Blueprint.H3.DepartureBalanceStatement := by
  intro n w z
  have h := shifted_filter_count_le
    (fun j => wordVertex AKLT.Defs.kernelStart w j) n z
  simpa [AKLT.Defs.departureCount, AKLT.Blueprint.H3.arrivalCount] using h

end AKLT.W.H3M012

#print axioms AKLT.W.H3M012.main
