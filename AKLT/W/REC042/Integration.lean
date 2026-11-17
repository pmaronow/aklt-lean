module
public import AKLT.W.REC002.Trace
public import AKLT.W.REC003.Trace
public import AKLT.W.REC042.Site

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC042

open AKLT.W.REC003

/-- Isolate a site with an inserted local function and an observable that
does not depend on that site. Original leg factors remain in the complement. -/
theorem partition_site {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (y : Plane) (hy : y ∈ D.active) (hyS : y ∉ protectedSites G)
    (g : Vec3 → ℝ) (f : (Plane → Vec3) → ℝ)
    (hf : ∀ m n, f (Function.update m y n) = f m) :
    D.partition τ b (fun m => g (m y) * f m) =
      (removeSite D y).partition τ b (fun m =>
        siteFunctional (D.status y)
          (fun n => g n * ∏ z ∈ D.presentNeighbors y, (1 + dot n (m z))) * f m) := by
  rw [partition_repr, partition_repr, removed_integral,
    spinIntegral_site D.active y hy]
  unfold spinIntegral
  apply Finset.sum_congr rfl
  intro σ _
  simp_rw [Function.update_self, hf, interaction_update D τ b y hyS]
  let m := extendSpins (D.active.erase y) σ
  change _ * siteFunctional (D.status y)
      (fun n => g n * f m * (interaction (removeSite D y) τ b m *
        ∏ z ∈ D.presentNeighbors y, (1 + dot n (m z)))) = _
  rw [show (fun n => g n * f m * (interaction (removeSite D y) τ b m *
      ∏ z ∈ D.presentNeighbors y, (1 + dot n (m z)))) =
      (fun n => (g n * ∏ z ∈ D.presentNeighbors y, (1 + dot n (m z))) *
        (f m * interaction (removeSite D y) τ b m)) by funext n; ring,
    site_mul_const]
  ring

/-- Removing a departure after changing its status preserves the complement. -/
theorem remove_trace_partition_all {G : Finset Plane} (D : Network G) (y o : Plane)
    (τ : PinAssignment G) (b : Bool) (f : (Plane → Vec3) → ℝ) :
    (removeSite (traceStep D y o) y).partition τ b f =
      (removeSite D y).partition τ b f := by
  apply AKLT.W.REC003.partition_congr
  · exact AKLT.W.REC002.remove_trace_status D y o
  · ext e
    rw [mem_remove_bonds, mem_remove_bonds]
    by_cases hx : e.1 = y
    · simp [hx]
    by_cases hz : e.2 = y
    · simp [hz]
    simp only [Network.bonds, Finset.mem_filter]
    have hsx : (traceStep D y o).status e.1 = D.status e.1 := by
      simp [traceStep, hx]
    have hsz : (traceStep D y o).status e.2 = D.status e.2 := by
      simp [traceStep, hz]
    simp only [Network.Present, Network.active, Finset.mem_filter, hsx, hsz,
      AKLT.W.REC002.trace_kept_away D y o e.1 e.2 hx hz,
      AKLT.W.REC002.trace_kept_away D y o e.2 e.1 hz hx]

/-- A non-U departure is removed, and erasing its incident flag has no
effect on the partition of the remaining sites. -/
theorem trace_partition_removed {G : Finset Plane} (D : Network G) (y o : Plane)
    (hy : D.status y ≠ .U) (τ : PinAssignment G) (b : Bool)
    (f : (Plane → Vec3) → ℝ) :
    (traceStep D y o).partition τ b f = (removeSite D y).partition τ b f := by
  have he : removeSite (traceStep D y o) y = traceStep D y o := by
    have hs : Function.update (traceStep D y o).status y .X =
        (traceStep D y o).status := by
      funext x
      by_cases hx : x = y <;> simp [traceStep, hx, hy]
    unfold removeSite
    rw [hs]
  rw [← he]
  exact remove_trace_partition_all D y o τ b f

/-- Departure integration for the two marked coordinates. -/
theorem partition_coordinate {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (u v : Plane) (hu : u ∈ D.active) (huS : u ∉ protectedSites G)
    (huv : u ≠ v) (k : Fin 3) :
    D.partition τ b (fun m => m u k * m v k) =
      (removeSite D u).partition τ b (fun m =>
        siteFunctional (D.status u)
          (fun n => n k * ∏ z ∈ D.presentNeighbors u, (1 + dot n (m z))) * m v k) := by
  exact partition_site D τ b u hu huS (fun n => n k) (fun m => m v k)
    (fun m n => by rw [Function.update_of_ne huv.symm])

/-- At a U departure the selected edge is deleted and the residual law is D. -/
theorem trace_partition_U {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (u v o : Plane) (hu : u ∈ D.active) (huS : u ∉ protectedSites G)
    (hU : D.status u = .U) (huv : u ≠ v) (ho : o ∈ D.presentNeighbors u)
    (k : Fin 3) :
    (traceStep D u o).partition τ b (fun m => m o k * m v k) =
      (removeSite D u).partition τ b (fun m =>
        siteFunctional .D
          (fun n => ∏ z ∈ (D.presentNeighbors u).erase o, (1 + dot n (m z))) *
        (m o k * m v k)) := by
  have huo : u ≠ o := adjacent_ne ((mem_presentNeighbors D u o).mp ho).2.2.1
  have hu' : u ∈ (traceStep D u o).active := by
    rw [trace_active D u o hU]
    exact hu
  have hs : (traceStep D u o).status u = .D := by simp [traceStep, hU]
  have hf : ∀ m : Plane → Vec3, ∀ n : Vec3,
      (Function.update m u n) o k * (Function.update m u n) v k = m o k * m v k := by
    intro m n
    rw [Function.update_of_ne huo.symm, Function.update_of_ne huv.symm]
  have h := partition_site (traceStep D u o) τ b u hu' huS
    (fun _ => 1) (fun m => m o k * m v k) hf
  simp only [one_mul, hs, trace_neighbors D u o hU huo] at h
  rw [remove_trace_partition_all] at h
  exact h

/-- Linearity of the finite unnormalized partition, for a finite index set. -/
theorem partition_finset_sum {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) {α : Type*} (s : Finset α) (f : α → (Plane → Vec3) → ℝ) :
    D.partition τ b (fun m => ∑ x ∈ s, f x m) = ∑ x ∈ s, D.partition τ b (f x) := by
  simp only [AKLT.W.REC002.partition_weight, Finset.mul_sum]
  rw [Finset.sum_comm]

end AKLT.W.REC042
