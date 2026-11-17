module
public import AKLT.W.REC017.Sums
public import AKLT.W.REC017.Bonds

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC017

def pinProduct {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (n : Plane → Vec3) : ℝ :=
  ∏ e : originalLegs G,
    if b = true ∧ e.val.1 ∈ D.active then 1 + dot (τ e).val (n e.val.1) else 1

theorem field_eq_spins {G : Finset Plane} (D : Network G) (n : D.active → SpinLetter) :
    field n = D.spins n := by
  funext x
  by_cases hx : x ∈ D.active <;> simp [field, letters, Network.spins, hx, spinVector]

theorem partition_quad {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (F : (Plane → Vec3) → ℝ) :
    D.partition τ b F = quadrature D.active D.status
      (fun n => F n * bondProduct D n * pinProduct D τ b n) := by
  unfold Network.partition quadrature
  apply Finset.sum_congr rfl
  intro n hn
  have hp : (∏ x ∈ D.active, spinWeight (D.status x) (letters n x)) =
      ∏ x : D.active, spinWeight (D.status x.val) (n x) := by
    rw [← Finset.prod_coe_sort]
    simp only [letters_mem]
  rw [hp, field_eq_spins]
  dsimp only [bondProduct, pinProduct]
  ring

theorem pinProduct_split {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (y : Plane) (hy : ∀ e : originalLegs G, e.val.1 ≠ y)
    (n : Plane → Vec3) (v : Vec3) :
    pinProduct D τ b (Function.update n y v) = pinProduct (removeSite D y) τ b n := by
  unfold pinProduct
  apply Finset.prod_congr rfl
  intro e he
  simp [remove_active, hy e]

theorem partition_integrate {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (y : Plane) (hy : y ∈ D.active)
    (hleg : ∀ e : originalLegs G, e.val.1 ≠ y) :
    D.partition τ b (fun _ => 1) =
      (removeSite D y).partition τ b (fun n => siteFunctional (D.status y)
        (fun v => ∏ z ∈ D.presentNeighbors y, (1 + dot v (n z)))) := by
  have hnot : y ∉ (removeSite D y).active := by simp [remove_active]
  have hs : D.active = insert y (removeSite D y).active := by
    rw [remove_active, Finset.insert_erase hy]
  rw [partition_quad, hs, quadrature_insert _ _ hnot, partition_quad]
  rw [quadrature_status_congr (removeSite D y).active D.status (removeSite D y).status
    (by
      intro x hx
      have hn := (Finset.mem_erase.mp (remove_active D y ▸ hx)).1
      simp [removeSite, Function.update_of_ne hn])]
  unfold quadrature
  apply Finset.sum_congr rfl
  intro n hn
  dsimp only
  simp_rw [one_mul, bondProduct_split, pinProduct_split D τ b y hleg]
  unfold siteFunctional
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  ring

theorem remove_trace_partition {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (y o : Plane) (hy : D.status y = .U)
    (F : (Plane → Vec3) → ℝ) :
    (removeSite (traceStep D y o) y).partition τ b F =
      (removeSite D y).partition τ b F := by
  have hstatus : (removeSite (traceStep D y o) y).status = (removeSite D y).status := by
    funext x
    by_cases hx : x = y <;> simp [removeSite, traceStep, hx]
  have hactive : (removeSite (traceStep D y o) y).active = (removeSite D y).active := by
    simp only [Network.active, hstatus]
  have hbonds : (removeSite (traceStep D y o) y).bonds = (removeSite D y).bonds := by
    ext e
    simp only [mem_bonds, remove_present, trace_present D y o e.1 e.2 hy]
    tauto
  rw [partition_quad, partition_quad, hactive, hstatus]
  congr 1
  funext n
  unfold bondProduct pinProduct
  rw [hbonds, hactive]

end AKLT.W.REC017
