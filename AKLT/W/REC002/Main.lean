import AKLT.W.REC002.Trace

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC002

open AKLT.Blueprint.Rec

theorem integrate_neighbours_three (o f g : Plane) (hof : o ≠ f) (hog : o ≠ g)
    (hfg : f ≠ g) (n : Plane → Vec3) :
    siteFunctional .U (fun v => ∏ z ∈ ({o, f, g} : Finset Plane), (1 + dot v (n z))) =
      1 + (dot (n f) (n g) + dot (n f) (n o) + dot (n g) (n o)) / 3 := by
  calc
    _ = siteFunctional .U
        (fun v => (1 + dot v (n f)) * (1 + dot v (n g)) * (1 + dot v (n o))) := by
      congr 1
      funext v
      simp [Finset.prod_insert, hof, hog, hfg]
      ring
    _ = _ := integrate_U3 (n f) (n g) (n o)

theorem integrate_neighbours_two (f g : Plane) (hfg : f ≠ g) (n : Plane → Vec3) :
    siteFunctional .D (fun v => ∏ z ∈ ({f, g} : Finset Plane), (1 + dot v (n z))) =
      1 + dot (n f) (n g) / 5 := by
  simpa [Finset.prod_insert, hfg] using integrate_D2 (n f) (n g)

theorem partition_div {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (c : ℝ) (f : (Plane → Vec3) → ℝ) :
    D.partition τ b (fun n => f n / c) = D.partition τ b f / c := by
  simp only [partition_weight, mul_div_assoc, Finset.sum_div]

theorem partition_three_expectations {G : Finset Plane} (D : Network G)
    (τ : PinAssignment G) (b : Bool) (o f g : Plane) :
    D.partition τ b (fun n => 1 +
      (dot (n f) (n g) + dot (n f) (n o) + dot (n g) (n o)) / 3) =
      D.partition τ b (fun _ => 1) * (1 +
        (D.expectation τ b (fun n => dot (n f) (n g)) +
         D.expectation τ b (fun n => dot (n f) (n o)) +
         D.expectation τ b (fun n => dot (n g) (n o))) / 3) := by
  simp only [partition_add, partition_div, mul_add, ← mul_div_assoc, mul_one,
    partition_expectation]

theorem partition_one_expectation {G : Finset Plane} (D : Network G)
    (τ : PinAssignment G) (b : Bool) (f g : Plane) :
    D.partition τ b (fun n => 1 + dot (n f) (n g) / 5) =
      D.partition τ b (fun _ => 1) *
        (1 + D.expectation τ b (fun n => dot (n f) (n g)) / 5) := by
  simp only [partition_add, partition_div, mul_add, ← mul_div_assoc, mul_one,
    partition_expectation]

/-- Integrating the unpinned departure gives the two exact local factors. -/
theorem main : AKLT.Blueprint.Rec.ThreeFactorizationStatement := by
  intro a hU f g hN hof hog hfg b
  have hleg := no_leg a.start
  have hyo : a.y ≠ a.o := present_ne ((mem_presentNeighbours a.D a.y a.o).mp a.present)
  constructor
  · calc
      a.D.partition a.τ b (fun _ => 1) =
          (removeSite a.D a.y).partition a.τ b
            (fun n => siteFunctional (a.D.status a.y)
              (fun v => ∏ z ∈ a.D.presentNeighbours a.y, (1 + dot v (n z)))) :=
        partition_integrate a.D a.y a.start.1 hleg a.τ b
      _ = (removeSite a.D a.y).partition a.τ b
          (fun n => 1 + (dot (n f) (n g) + dot (n f) (n a.o) + dot (n g) (n a.o)) / 3) := by
        simp_rw [hU, hN, integrate_neighbours_three a.o f g hof hog hfg]
      _ = _ := partition_three_expectations (removeSite a.D a.y) a.τ b a.o f g
  · have hy : a.y ∈ (traceStep a.D a.y a.o).active := by
      rw [trace_active a.D a.y a.o hU]
      exact a.start.1
    have hD : (traceStep a.D a.y a.o).status a.y = .D := by
      simp [traceStep, hU]
    have hN' : (traceStep a.D a.y a.o).presentNeighbours a.y = {f, g} := by
      rw [trace_neighbours a.D a.y a.o hU hyo, hN]
      simp [hof, hog]
    calc
      (traceStep a.D a.y a.o).partition a.τ b (fun _ => 1) =
          (removeSite (traceStep a.D a.y a.o) a.y).partition a.τ b
            (fun n => siteFunctional ((traceStep a.D a.y a.o).status a.y)
              (fun v => ∏ z ∈ (traceStep a.D a.y a.o).presentNeighbours a.y,
                (1 + dot v (n z)))) :=
        partition_integrate (traceStep a.D a.y a.o) a.y hy hleg a.τ b
      _ = (removeSite a.D a.y).partition a.τ b
          (fun n => 1 + dot (n f) (n g) / 5) := by
        rw [remove_trace_partition a.D a.y a.o hU]
        simp_rw [hD, hN', integrate_neighbours_two f g hfg]
      _ = _ := partition_one_expectation (removeSite a.D a.y) a.τ b f g

end AKLT.W.REC002
