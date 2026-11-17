module
public import AKLT.W.REC091.Remove

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC091

theorem bondWeights_insert {G : Finset Plane} (D : Network G) (y : Plane)
    (hy : y ∈ D.active) (j : SpinLetter) (m : (removeSite D y).active → SpinLetter) :
    (∏ e ∈ D.bonds, (1 + dot (D.spins (insertSpin D y hy j m) e.1)
      (D.spins (insertSpin D y hy j m) e.2))) =
    (∏ e ∈ (removeSite D y).bonds,
      (1 + dot ((removeSite D y).spins m e.1) ((removeSite D y).spins m e.2))) *
    ∏ z ∈ D.presentNeighbors y, (1 + dot (spinVector j) ((removeSite D y).spins m z)) := by
  classical
  let p : Plane × Plane → Prop := fun e => e.1 = y ∨ e.2 = y
  let F : Plane × Plane → ℝ := fun e =>
    1 + dot (D.spins (insertSpin D y hy j m) e.1) (D.spins (insertSpin D y hy j m) e.2)
  have hn : D.bonds.filter (fun e => ¬p e) = (removeSite D y).bonds := by
    rw [remove_bonds]
    apply Finset.filter_congr
    intro e _
    simp only [p, not_or]
  have hnot : (∏ e ∈ D.bonds.filter (fun e => ¬p e), F e) =
      ∏ e ∈ (removeSite D y).bonds,
        (1 + dot ((removeSite D y).spins m e.1) ((removeSite D y).spins m e.2)) := by
    rw [hn]
    apply Finset.prod_congr rfl
    intro e he
    have he' := Finset.mem_filter.mp (remove_bonds D y ▸ he)
    exact congrArg (fun t : ℝ => 1 + t) (congrArg₂ dot
      (spins_insert_ne D y hy j m he'.2.1) (spins_insert_ne D y hy j m he'.2.2))
  have hinc : (∏ e ∈ D.bonds.filter p, F e) =
      ∏ z ∈ D.presentNeighbors y,
        (1 + dot (spinVector j) ((removeSite D y).spins m z)) := by
    rw [← incident_image D y, Finset.prod_image (incident_injective D y)]
    apply Finset.prod_congr rfl
    intro e he
    have hi := (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).1
    have hne := positive_neighbor_ne (mem_internalBonds.mp hi).2.2
    by_cases he1 : e.1 = y
    · have he2 : e.2 ≠ y := by simpa [he1] using hne
      simp only [F, otherEndpoint, he1, ite_true,
        spins_insert_y, spins_insert_ne D y hy j m he2]
    · have he2 : e.2 = y := (Finset.mem_filter.mp he).2.resolve_left he1
      simp only [F, otherEndpoint, ite_eq_right he1, he2,
        spins_insert_y, spins_insert_ne D y hy j m he1]
      rw [dot_comm]
  change (∏ e ∈ D.bonds, F e) = _
  rw [← Finset.prod_filter_not_mul_prod_filter D.bonds p F, hnot, hinc]

theorem legWeights_insert {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (y : Plane) (hy : y ∈ D.active)
    (hleg : ∀ e : originalLegs G, e.val.1 ≠ y)
    (j : SpinLetter) (m : (removeSite D y).active → SpinLetter) :
    (∏ e : originalLegs G,
      if b = true ∧ e.val.1 ∈ D.active then
        1 + dot (τ e).val (D.spins (insertSpin D y hy j m) e.val.1) else 1) =
    ∏ e : originalLegs G,
      if b = true ∧ e.val.1 ∈ (removeSite D y).active then
        1 + dot (τ e).val ((removeSite D y).spins m e.val.1) else 1 := by
  apply Finset.prod_congr rfl
  intro e _
  by_cases hb : b = true
  · by_cases ha : e.val.1 ∈ D.active
    · have he := (mem_remove_active D y e.val.1).mpr ⟨hleg e, ha⟩
      simp only [hb, ha, he, and_self, ite_true, spins_insert_ne D y hy j m (hleg e)]
    · have he : e.val.1 ∉ (removeSite D y).active := fun h =>
        ha ((mem_remove_active D y e.val.1).mp h).2
      simp [ha, he]
  · simp [hb]

theorem networkWeight_insert {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (y : Plane) (hy : y ∈ D.active)
    (hleg : ∀ e : originalLegs G, e.val.1 ≠ y)
    (j : SpinLetter) (m : (removeSite D y).active → SpinLetter) :
    networkWeight D τ b (insertSpin D y hy j m) =
      networkWeight (removeSite D y) τ b m * spinWeight (D.status y) j *
        ∏ z ∈ D.presentNeighbors y,
          (1 + dot (spinVector j) ((removeSite D y).spins m z)) := by
  unfold networkWeight
  rw [siteWeights_insert, bondWeights_insert, legWeights_insert D τ b y hy hleg]
  ring

/-- Finite Fubini at one site, with all original pins retained at the other sites. -/
theorem partition_integrate_site {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (y : Plane) (hy : y ∈ D.active)
    (hleg : ∀ e : originalLegs G, e.val.1 ≠ y) :
    D.partition τ b (fun _ => 1) =
      (removeSite D y).partition τ b (fun n => siteFunctional (D.status y)
        (fun v => ∏ z ∈ D.presentNeighbors y, (1 + dot v (n z)))) := by
  rw [partition_eq_sum_weight, ← Equiv.sum_comp (removalConfigEquiv D y hy).symm,
    Fintype.sum_prod_type, Finset.sum_comm, partition_eq_sum_weight]
  apply Finset.sum_congr rfl
  intro m _
  simp only [removalConfigEquiv_symm, networkWeight_insert D τ b y hy hleg, mul_one,
    siteFunctional, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

end AKLT.W.REC091
