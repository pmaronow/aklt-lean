module
public import AKLT.Blueprint.Rec.NodesResponse
public import AKLT.W.REC003.Trace
public import AKLT.W.REC003.Weights

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Rec

namespace AKLT.W.REC003

/-- Integrating the two U bonds gives the prescribed normalized I₂ factor. -/
theorem pre_factorization (a : Departure) (hy : a.D.status a.y = .U) (f : Plane)
    (hneigh : a.D.presentNeighbours a.y = {a.o, f}) (hof : a.o ≠ f) (b : Bool) :
    a.D.partition a.τ b (fun _ => 1) =
      (removeSite a.D a.y).partition a.τ b (fun _ => 1) * responseI₂ a.D a.τ b a.y a.o f := by
  have h := partition_eliminate a.D a.τ b a.y a.start.1 a.start.2.1
  have hi : a.D.partition a.τ b (fun _ => 1) =
      (removeSite a.D a.y).partition a.τ b (fun m => 1 + dot (m f) (m a.o) / 3) := by
    rw [h]
    congr 1
    funext m
    simp only [hy, hneigh, Finset.prod_pair hof]
    rw [site_U_two, dot_comm]
  rw [hi, partition_add, partition_div]
  unfold responseI₂ removedPairMean
  rw [mul_add, mul_one, ← mul_div_assoc, partition_mul_expectation]

/-- The trace leaves one D bond, whose site sum is one. -/
theorem post_factorization (a : Departure) (hy : a.D.status a.y = .U) (f : Plane)
    (hneigh : a.D.presentNeighbours a.y = {a.o, f}) (hof : a.o ≠ f) (b : Bool) :
    (traceStep a.D a.y a.o).partition a.τ b (fun _ => 1) =
      (removeSite a.D a.y).partition a.τ b (fun _ => 1) := by
  have hyo : a.y ≠ a.o := adjacent_ne ((mem_presentNeighbours _ _ _).mp a.present).2.2.1
  have ha : a.y ∈ (traceStep a.D a.y a.o).active := by
    rw [trace_active a.D a.y a.o hy]
    exact a.start.1
  have hs : (traceStep a.D a.y a.o).status a.y = .D := by
    simp [traceStep, hy]
  have hn : (traceStep a.D a.y a.o).presentNeighbours a.y = {f} := by
    rw [trace_neighbours a.D a.y a.o hy hyo, hneigh]
    simp [hof]
  have h := partition_eliminate (traceStep a.D a.y a.o) a.τ b a.y ha a.start.2.1
  have hfun : (fun m : Plane → Vec3 => siteFunctional ((traceStep a.D a.y a.o).status a.y)
      (fun v => ∏ z ∈ (traceStep a.D a.y a.o).presentNeighbours a.y, (1 + dot v (m z)))) =
      (fun _ => 1) := by
    funext m
    simp only [hs, hn, Finset.prod_singleton]
    exact site_D_one _
  rw [hfun, remove_trace_partition a.D a.y a.o hy] at h
  exact h

theorem main : AKLT.Blueprint.Rec.TwoFactorizationStatement := by
  intro a hy f hneigh hof b
  exact ⟨pre_factorization a hy f hneigh hof b, post_factorization a hy f hneigh hof b⟩

#print axioms main

end AKLT.W.REC003
