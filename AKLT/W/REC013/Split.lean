module
public import AKLT.W.REC013.NetworkFacts

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC013

variable {G : Finset Plane} (D : Network G) (y : Plane) (hy : y ∈ D.active)

def joinSpin (j : SpinLetter) (n : (removeSite D y).active → SpinLetter) :
    D.active → SpinLetter :=
  fun x => if h : x.val = y then j else n ⟨x.val, (remove_active D y x.val).2 ⟨x.property, h⟩⟩

def splitSpin : (D.active → SpinLetter) ≃
    SpinLetter × ((removeSite D y).active → SpinLetter) where
  toFun m := (m ⟨y, hy⟩, fun x => m ⟨x.val, ((remove_active D y x.val).1 x.property).1⟩)
  invFun p := joinSpin D y p.1 p.2
  left_inv m := by
    funext x
    dsimp only [joinSpin]
    split_ifs with h
    · congr 1
      exact Subtype.ext h.symm
    · rfl
  right_inv p := by
    rcases p with ⟨j,n⟩
    apply Prod.ext
    · simp [joinSpin]
    · funext x
      simp only [joinSpin]
      rw [dite_eq_right ((remove_active D y x.val).1 x.property).2]

/-- The site index itself splits into the removed site and the remaining sites. -/
def siteEquiv : Option (removeSite D y).active ≃ D.active where
  toFun
    | none => ⟨y,hy⟩
    | some x => ⟨x.val, ((remove_active D y x.val).1 x.property).1⟩
  invFun x := if h : x.val = y then none
    else some ⟨x.val, (remove_active D y x.val).2 ⟨x.property,h⟩⟩
  left_inv x := by
    cases x with
    | none => simp
    | some x => simp [((remove_active D y x.val).1 x.property).2]
  right_inv x := by
    dsimp only
    split_ifs with h
    · exact Subtype.ext h.symm
    · rfl

include hy in
theorem sum_split (F : (D.active → SpinLetter) → ℝ) :
    (∑ m, F m) = ∑ n : (removeSite D y).active → SpinLetter,
      ∑ j : SpinLetter, F (joinSpin D y j n) := by
  rw [← (splitSpin D y hy).symm.sum_comp F, Fintype.sum_prod_type, Finset.sum_comm]
  rfl

include hy in
theorem join_weight (j : SpinLetter) (n : (removeSite D y).active → SpinLetter) :
    (∏ x : D.active, spinWeight (D.status x.val) (joinSpin D y j n x)) =
      spinWeight (D.status y) j *
        ∏ x : (removeSite D y).active, spinWeight ((removeSite D y).status x.val) (n x) := by
  rw [← (siteEquiv D y hy).prod_comp (fun x => spinWeight (D.status x.val) (joinSpin D y j n x)),
    Fintype.prod_option]
  congr 1
  · simp [siteEquiv, joinSpin]
  · apply Finset.prod_congr rfl
    intro x _
    have hx := ((remove_active D y x.val).1 x.property).2
    change spinWeight (D.status x.val)
      (joinSpin D y j n ⟨x.val, ((remove_active D y x.val).1 x.property).1⟩) =
      spinWeight ((removeSite D y).status x.val) (n x)
    simp [joinSpin, removeSite, hx]
    rfl

include hy in
@[simp] theorem join_spins_y (j : SpinLetter) (n : (removeSite D y).active → SpinLetter) :
    D.spins (joinSpin D y j n) y = spinVector j := by
  simp [Network.spins, hy, joinSpin]

theorem join_spins_ne (j : SpinLetter) (n : (removeSite D y).active → SpinLetter)
    {x : Plane} (hx : x ≠ y) :
    D.spins (joinSpin D y j n) x = (removeSite D y).spins n x := by
  by_cases ha : x ∈ D.active
  · have he : x ∈ (removeSite D y).active := (remove_active D y x).2 ⟨ha,hx⟩
    simp [Network.spins, ha, he, joinSpin, hx]
  · have he : x ∉ (removeSite D y).active := by simp [ha]
    simp [Network.spins, ha, he]

end AKLT.W.REC013
