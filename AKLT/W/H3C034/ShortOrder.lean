module
public import AKLT.W.H3C034.Words
public import AKLT.W.H3C032.Main
public import Mathlib.Data.List.Sort

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Cert.H3 AKLT.Cert.H3.Production CertData.H3.Bridge

namespace AKLT.W.H3C034

set_option maxHeartbeats 200000

def shortScore {n : Nat} (w : DirectionWord n) (i : Fin n) : WithTop ℚ :=
  if witnessKappa w i = 0 then ⊤ else
    (((passageFactor (wordStraight kernelIncoming w i)-1) /
      (passageFactor (wordStraight kernelIncoming w i)*witnessKappa w i) : ℚ) : WithTop ℚ)

theorem shortOrder_iff {n : Nat} (w : DirectionWord n) (i j : Fin n) :
    shortOrderLE w i j = true ↔ shortScore w i < shortScore w j ∨
      (shortScore w i = shortScore w j ∧ i.val ≤ j.val) := by
  by_cases hi : witnessKappa w i = 0 <;> by_cases hj : witnessKappa w j = 0 <;>
    simp [shortOrderLE, shortScore, hi, hj]

theorem shortOrder_trans {n : Nat} (w : DirectionWord n) (i j k : Fin n)
    (hij : shortOrderLE w i j = true) (hjk : shortOrderLE w j k = true) :
    shortOrderLE w i k = true := by
  rw [shortOrder_iff] at hij hjk ⊢
  rcases hij with h | ⟨h, hi⟩ <;> rcases hjk with h' | ⟨h', hj⟩
  · exact Or.inl (lt_trans h h')
  · exact Or.inl (lt_of_lt_of_eq h h')
  · exact Or.inl (lt_of_eq_of_lt h h')
  · exact Or.inr ⟨h.trans h', hi.trans hj⟩

theorem shortOrder_total {n : Nat} (w : DirectionWord n) (i j : Fin n) :
    (shortOrderLE w i j || shortOrderLE w j i) = true := by
  simp only [Bool.or_eq_true, shortOrder_iff]
  rcases lt_trichotomy (shortScore w i) (shortScore w j) with h | h | h
  · exact Or.inl (Or.inl h)
  · rcases le_total i.val j.val with ht | ht
    · exact Or.inl (Or.inr ⟨h, ht⟩)
    · exact Or.inr (Or.inr ⟨h.symm, ht⟩)
  · exact Or.inr (Or.inl h)

theorem shortOrder_antisymm {n : Nat} (w : DirectionWord n) (i j : Fin n)
    (hij : shortOrderLE w i j = true) (hji : shortOrderLE w j i = true) : i=j := by
  rw [shortOrder_iff] at hij hji
  rcases hij with h | ⟨h, hi⟩ <;> rcases hji with h' | ⟨h', hj⟩
  · exact False.elim (lt_asymm h h')
  · exact False.elim (ne_of_lt h h'.symm)
  · exact False.elim (ne_of_lt h' h.symm)
  · exact Fin.ext (Nat.le_antisymm hi hj)

theorem sort_reverse {n : Nat} (w : DirectionWord n) (xs : List (Fin n)) :
    xs.reverse.mergeSort (shortOrderLE w) = xs.mergeSort (shortOrderLE w) := by
  have h₁ := List.pairwise_mergeSort (le := shortOrderLE w)
    (shortOrder_trans w) (shortOrder_total w) xs.reverse
  have h₂ := List.pairwise_mergeSort (le := shortOrderLE w)
    (shortOrder_trans w) (shortOrder_total w) xs
  have hp : (xs.reverse.mergeSort (shortOrderLE w)).Perm (xs.mergeSort (shortOrderLE w)) :=
    (List.mergeSort_perm _ _).trans
      ((List.reverse_perm xs).trans (List.mergeSort_perm _ _).symm)
  exact List.Perm.eq_of_pairwise (le := fun i j : Fin n => shortOrderLE w i j = true)
    (fun i j _ _ hij hji => shortOrder_antisymm w i j hij hji) h₁ h₂ hp

end AKLT.W.H3C034
