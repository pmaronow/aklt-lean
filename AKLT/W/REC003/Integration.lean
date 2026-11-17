module
public import AKLT.W.REC003.Finite
public import AKLT.W.REC003.Geometry
public import AKLT.W.REC003.Moments

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC003

def bondProduct {G : Finset Plane} (D : Network G) (m : Plane → Vec3) : ℝ :=
  ∏ e ∈ D.bonds, (1 + dot (m e.1) (m e.2))

def legProduct {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (m : Plane → Vec3) : ℝ :=
  ∏ e : originalLegs G,
    if b = true ∧ e.val.1 ∈ D.active then 1 + dot (τ e).val (m e.val.1) else 1

def interaction {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (m : Plane → Vec3) : ℝ := bondProduct D m * legProduct D τ b m

theorem bondProduct_update {G : Finset Plane} (D : Network G) (y : Plane)
    (m : Plane → Vec3) (v : Vec3) :
    bondProduct D (Function.update m y v) = bondProduct (removeSite D y) m *
      ∏ z ∈ D.presentNeighbours y, (1 + dot v (m z)) := by
  unfold bondProduct
  rw [bonds_split D y, Finset.prod_union (bonds_split_disjoint D y)]
  congr 1
  · apply Finset.prod_congr rfl
    intro e he
    have hn := ((mem_remove_bonds D y e).mp he).2
    rw [Function.update_of_ne hn.1, Function.update_of_ne hn.2]
  · rw [Finset.prod_image (fun _ _ _ _ h => edge_injective y h)]
    apply Finset.prod_congr rfl
    intro z hz
    have hzy : z ≠ y := (adjacent_ne ((mem_presentNeighbours D y z).mp hz).2.2.1).symm
    rcases edge_cases y z with he | he
    · simp only [he, Function.update_self, Function.update_of_ne hzy]
    · simp only [he, Function.update_self, Function.update_of_ne hzy]
      rw [dot_comm]

theorem legProduct_update {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (y : Plane) (hy : y ∉ protectedSites G) (m : Plane → Vec3) (v : Vec3) :
    legProduct D τ b (Function.update m y v) = legProduct (removeSite D y) τ b m := by
  unfold legProduct
  apply Finset.prod_congr rfl
  intro e _
  have hn := no_original_leg hy e
  rw [Function.update_of_ne hn, remove_active]
  simp only [Finset.mem_erase]
  apply if_congr
  · tauto
  · rfl
  · rfl

theorem interaction_update {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (y : Plane) (hy : y ∉ protectedSites G) (m : Plane → Vec3) (v : Vec3) :
    interaction D τ b (Function.update m y v) = interaction (removeSite D y) τ b m *
      ∏ z ∈ D.presentNeighbours y, (1 + dot v (m z)) := by
  unfold interaction
  rw [bondProduct_update, legProduct_update D τ b y hy]
  ring

theorem partition_repr {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (f : (Plane → Vec3) → ℝ) :
    D.partition τ b f = spinIntegral D.active D.status (fun m => f m * interaction D τ b m) := by
  unfold Network.partition spinIntegral interaction bondProduct legProduct
  apply Finset.sum_congr rfl
  intro n _
  change _ = (∏ x : D.active, spinWeight (D.status x) (n x)) *
    (f (D.spins n) * ((∏ e ∈ D.bonds, (1 + dot (D.spins n e.1) (D.spins n e.2))) *
      ∏ e : originalLegs G,
        if b = true ∧ e.val.1 ∈ D.active then 1 + dot (τ e).val (D.spins n e.val.1) else 1))
  ring

theorem removed_integral {G : Finset Plane} (D : Network G) (y : Plane)
    (H : (Plane → Vec3) → ℝ) :
    spinIntegral (removeSite D y).active (removeSite D y).status H =
      spinIntegral (D.active.erase y) D.status H := by
  rw [remove_active]
  apply spinIntegral_status
  intro x hx
  exact Function.update_of_ne (Finset.ne_of_mem_erase hx) _ _

/-- Exact departure integration, retaining the original pins and all remaining bonds. -/
theorem partition_eliminate {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (y : Plane) (hy : y ∈ D.active) (hyS : y ∉ protectedSites G) :
    D.partition τ b (fun _ => 1) = (removeSite D y).partition τ b
      (fun m => siteFunctional (D.status y)
        (fun v => ∏ z ∈ D.presentNeighbours y, (1 + dot v (m z)))) := by
  rw [partition_repr, partition_repr, removed_integral]
  simp only [one_mul]
  rw [spinIntegral_site D.active y hy]
  unfold spinIntegral
  apply Finset.sum_congr rfl
  intro n _
  simp_rw [interaction_update D τ b y hyS]
  have hfun : (fun v => interaction (removeSite D y) τ b (extendSpins (D.active.erase y) n) *
      ∏ z ∈ D.presentNeighbours y, (1 + dot v (extendSpins (D.active.erase y) n z))) =
      (fun v => (∏ z ∈ D.presentNeighbours y, (1 + dot v (extendSpins (D.active.erase y) n z))) *
        interaction (removeSite D y) τ b (extendSpins (D.active.erase y) n)) := by
    funext v
    exact mul_comm _ _
  rw [hfun, site_mul_const]

end AKLT.W.REC003
