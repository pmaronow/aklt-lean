module
public import AKLT.W.REC022.Geometry

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC022

variable {G : Finset Plane}

def netWeight (D : Network G) (τ : PinAssignment G) (b : Bool)
    (σ : D.active → SpinLetter) : ℝ :=
  (∏ x : D.active, spinWeight (D.status x.val) (σ x)) *
    (∏ e ∈ D.bonds, (1 + dot (D.spins σ e.1) (D.spins σ e.2))) *
    ∏ e : originalLegs G,
      if b = true ∧ e.val.1 ∈ D.active then
        1 + dot (τ e).val (D.spins σ e.val.1) else 1

theorem partition_sum (D : Network G) (τ : PinAssignment G) (b : Bool)
    (f : (Plane → Vec3) → ℝ) :
    D.partition τ b f = ∑ σ, netWeight D τ b σ * f (D.spins σ) := by
  unfold Network.partition netWeight
  apply Finset.sum_congr rfl
  intro σ _
  ring

theorem spins_ball (D : Network G) (σ : D.active → SpinLetter) (x : Plane) :
    normSq (D.spins σ x) ≤ 1 := by
  unfold Network.spins
  split
  · exact spin_ball _
  · norm_num [normSq, dot]

theorem netWeight_nonneg (D : Network G) (τ : PinAssignment G) (b : Bool)
    (σ : D.active → SpinLetter) : 0 ≤ netWeight D τ b σ := by
  apply mul_nonneg
  · apply mul_nonneg
    · exact Finset.prod_nonneg fun _ _ => weight_nonneg _ _
    · exact Finset.prod_nonneg fun e _ =>
        ball_factor _ _ (spins_ball D σ e.1) (spins_ball D σ e.2)
  · apply Finset.prod_nonneg
    intro e _
    split
    · exact ball_factor _ _ (τ e).property.le (spins_ball D σ e.val.1)
    · norm_num

def siteIndexEquiv (D : Network G) (y : Plane) (hy : y ∈ D.active) :
    D.active ≃ Option (removeSite D y).active where
  toFun x := if h : x.val = y then none
    else some ⟨x.val, by rw [active_remove]; exact Finset.mem_erase.mpr ⟨h,x.property⟩⟩
  invFun x := match x with
    | none => ⟨y,hy⟩
    | some z => ⟨z.val, by
        exact ((mem_active_remove D y z.val).mp z.property).2⟩
  left_inv x := by
    by_cases he : x.val = y
    · simp [he]
      exact Subtype.ext he.symm
    · simp [he]
  right_inv x := by
    cases x with
    | none => simp
    | some z =>
      have hn : z.val ≠ y := by
        exact ((mem_active_remove D y z.val).mp z.property).1
      simp [hn]

def joinSpin (D : Network G) (y : Plane) (hy : y ∈ D.active)
    (p : SpinLetter × ((removeSite D y).active → SpinLetter)) : D.active → SpinLetter :=
  fun x => match siteIndexEquiv D y hy x with
    | none => p.1
    | some z => p.2 z

def splitSpin (D : Network G) (y : Plane) (hy : y ∈ D.active) :
    (D.active → SpinLetter) ≃ SpinLetter × ((removeSite D y).active → SpinLetter) :=
  (Equiv.arrowCongr (siteIndexEquiv D y hy) (Equiv.refl SpinLetter)).trans
    (Equiv.piOptionEquivProd (β := fun _ : Option (removeSite D y).active => SpinLetter))

theorem splitSpin_symm (D : Network G) (y : Plane) (hy : y ∈ D.active)
    (p : SpinLetter × ((removeSite D y).active → SpinLetter)) :
    (splitSpin D y hy).symm p = joinSpin D y hy p := by
  funext x
  change Option.casesOn (motive := fun _ => SpinLetter)
    (siteIndexEquiv D y hy x) p.1 p.2 = joinSpin D y hy p x
  unfold joinSpin
  cases siteIndexEquiv D y hy x <;> rfl

theorem join_spins (D : Network G) (y : Plane) (hy : y ∈ D.active)
    (p : SpinLetter × ((removeSite D y).active → SpinLetter)) (x : Plane) :
    D.spins (joinSpin D y hy p) x =
      if x = y then spinVector p.1 else (removeSite D y).spins p.2 x := by
  by_cases he : x = y
  · subst x
    simp [Network.spins, hy, joinSpin, siteIndexEquiv]
  · by_cases ha : x ∈ D.active
    · have hm : x ∈ (removeSite D y).active := by
        rw [active_remove]; exact Finset.mem_erase.mpr ⟨he,ha⟩
      simp [Network.spins, ha, hm, he, joinSpin, siteIndexEquiv]
    · have hm : x ∉ (removeSite D y).active := by
        rw [active_remove]; simp [ha]
      simp [Network.spins,ha,hm,he]

theorem join_weights (D : Network G) (y : Plane) (hy : y ∈ D.active)
    (p : SpinLetter × ((removeSite D y).active → SpinLetter)) :
    (∏ x : D.active, spinWeight (D.status x.val) (joinSpin D y hy p x)) =
      spinWeight (D.status y) p.1 *
        ∏ x : (removeSite D y).active, spinWeight ((removeSite D y).status x.val) (p.2 x) := by
  let f : Option (removeSite D y).active → ℝ := fun x => match x with
    | none => spinWeight (D.status y) p.1
    | some z => spinWeight ((removeSite D y).status z.val) (p.2 z)
  calc
    _ = ∏ x : Option (removeSite D y).active, f x := by
      apply Fintype.prod_equiv (siteIndexEquiv D y hy)
      intro x
      by_cases he : x.val = y
      · simp [f,joinSpin,siteIndexEquiv,he]
      · have hi : siteIndexEquiv D y hy x = some
            (⟨x.val, (mem_active_remove D y x.val).mpr ⟨he,x.property⟩⟩ :
              (removeSite D y).active) := by
          exact dite_eq_right he
        change spinWeight (D.status x.val)
          (match siteIndexEquiv D y hy x with | none => p.1 | some z => p.2 z) =
          f (siteIndexEquiv D y hy x)
        rw [hi]
        change spinWeight (D.status x.val) _ =
          spinWeight (Function.update D.status y .X x.val) _
        rw [Function.update_of_ne he]
    _ = _ := by simp [f, Fintype.prod_option]

end AKLT.W.REC022
