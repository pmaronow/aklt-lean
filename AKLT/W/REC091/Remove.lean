import AKLT.W.REC091.Graph

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC091

theorem remove_active {G : Finset Plane} (D : Network G) (y : Plane) :
    (removeSite D y).active = D.active.erase y := by
  classical
  ext x
  simp only [Network.active, Finset.mem_erase, Finset.mem_filter]
  by_cases hx : x = y
  · subst x
    simp [removeSite]
  · simp [removeSite, hx]

theorem mem_remove_active {G : Finset Plane} (D : Network G) (y x : Plane) :
    x ∈ (removeSite D y).active ↔ x ≠ y ∧ x ∈ D.active := by
  rw [remove_active, Finset.mem_erase]

theorem remove_bonds {G : Finset Plane} (D : Network G) (y : Plane) :
    (removeSite D y).bonds = D.bonds.filter (fun e => e.1 ≠ y ∧ e.2 ≠ y) := by
  classical
  ext e
  rw [Network.bonds, Finset.mem_filter, Finset.mem_filter, Network.bonds, Finset.mem_filter]
  simp only [Network.Present, mem_remove_active]
  have hk : (removeSite D y).kept = D.kept := rfl
  rw [hk]
  tauto

def removalSiteEquiv {G : Finset Plane} (D : Network G) (y : Plane) (hy : y ∈ D.active) :
    Option (removeSite D y).active ≃ D.active := by
  classical
  exact
    { toFun := fun z => match z with
        | none => ⟨y, hy⟩
        | some z => ⟨z.val, (mem_remove_active D y z.val).mp z.property |>.2⟩
      invFun := fun x => if h : x.val = y then none else
        some ⟨x.val, (mem_remove_active D y x.val).mpr ⟨h, x.property⟩⟩
      left_inv := by
        intro z
        cases z with
        | none => simp
        | some z =>
          have hz := ((mem_remove_active D y z.val).mp z.property).1
          simp [hz]
      right_inv := by
        intro x
        by_cases hx : x.val = y
        · simp only [hx, dite_eq_left]
          exact Subtype.ext hx.symm
        · simp [hx] }

def insertSpin {G : Finset Plane} (D : Network G) (y : Plane) (hy : y ∈ D.active)
    (j : SpinLetter) (m : (removeSite D y).active → SpinLetter) : D.active → SpinLetter :=
  fun x => ((Equiv.piOptionEquivProd
    (β := fun _ : Option (removeSite D y).active => SpinLetter)).symm (j, m))
      ((removalSiteEquiv D y hy).symm x)

def removalConfigEquiv {G : Finset Plane} (D : Network G) (y : Plane) (hy : y ∈ D.active) :
    (D.active → SpinLetter) ≃ SpinLetter × ((removeSite D y).active → SpinLetter) :=
  (Equiv.arrowCongr (removalSiteEquiv D y hy).symm (Equiv.refl SpinLetter)).trans
    Equiv.piOptionEquivProd

theorem removalConfigEquiv_symm {G : Finset Plane} (D : Network G) (y : Plane)
    (hy : y ∈ D.active) (j : SpinLetter) (m : (removeSite D y).active → SpinLetter) :
    (removalConfigEquiv D y hy).symm (j, m) = insertSpin D y hy j m := rfl

theorem insertSpin_y {G : Finset Plane} (D : Network G) (y : Plane) (hy : y ∈ D.active)
    (j : SpinLetter) (m : (removeSite D y).active → SpinLetter) :
    insertSpin D y hy j m ⟨y, hy⟩ = j := by
  simp [insertSpin, removalSiteEquiv, Equiv.piOptionEquivProd]

theorem insertSpin_ne {G : Finset Plane} (D : Network G) (y : Plane) (hy : y ∈ D.active)
    (j : SpinLetter) (m : (removeSite D y).active → SpinLetter) (x : D.active)
    (hx : x.val ≠ y) : insertSpin D y hy j m x =
      m ⟨x.val, (mem_remove_active D y x.val).mpr ⟨hx, x.property⟩⟩ := by
  simp [insertSpin, removalSiteEquiv, Equiv.piOptionEquivProd, hx]

theorem spins_insert_y {G : Finset Plane} (D : Network G) (y : Plane) (hy : y ∈ D.active)
    (j : SpinLetter) (m : (removeSite D y).active → SpinLetter) :
    D.spins (insertSpin D y hy j m) y = spinVector j := by
  simp only [Network.spins, dite_eq_left hy, insertSpin_y]

theorem spins_insert_ne {G : Finset Plane} (D : Network G) (y : Plane) (hy : y ∈ D.active)
    (j : SpinLetter) (m : (removeSite D y).active → SpinLetter) {x : Plane} (hx : x ≠ y) :
    D.spins (insertSpin D y hy j m) x = (removeSite D y).spins m x := by
  by_cases hxa : x ∈ D.active
  · have hxe := (mem_remove_active D y x).mpr ⟨hx, hxa⟩
    simp only [Network.spins, dite_eq_left hxa, dite_eq_left hxe]
    rw [insertSpin_ne D y hy j m ⟨x, hxa⟩ hx]
  · have hxe : x ∉ (removeSite D y).active := fun h =>
      hxa ((mem_remove_active D y x).mp h).2
    simp only [Network.spins, dite_eq_right hxa, dite_eq_right hxe]

theorem siteWeights_insert {G : Finset Plane} (D : Network G) (y : Plane)
    (hy : y ∈ D.active) (j : SpinLetter) (m : (removeSite D y).active → SpinLetter) :
    (∏ x : D.active, spinWeight (D.status x.val) (insertSpin D y hy j m x)) =
      spinWeight (D.status y) j *
        ∏ x : (removeSite D y).active, spinWeight ((removeSite D y).status x.val) (m x) := by
  rw [← Equiv.prod_comp (removalSiteEquiv D y hy), Fintype.prod_option]
  apply congrArg₂ (fun a b : ℝ => a * b)
  · exact congrArg (spinWeight (D.status y)) (insertSpin_y D y hy j m)
  · apply Finset.prod_congr rfl
    intro x _
    have hx := ((mem_remove_active D y x.val).mp x.property).1
    simp only [removalSiteEquiv, Equiv.coe_fn_mk]
    rw [insertSpin_ne D y hy j m _ hx]
    simp [removeSite, Function.update_of_ne hx]
    congr 2

end AKLT.W.REC091
