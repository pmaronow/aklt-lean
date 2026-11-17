import AKLT.W.REC017.Network
import AKLT.W.REC017.Bounds

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Rec

namespace AKLT.W.REC017

theorem two_partition_raw (a : Departure) (hU : a.D.status a.y = .U) (f : Plane)
    (hN : a.D.presentNeighbours a.y = {a.o, f}) (hne : a.o ≠ f) (b : Bool) :
    a.D.partition a.τ b (fun _ => 1) =
      (removeSite a.D a.y).partition a.τ b (fun _ => 1) +
        (removeSite a.D a.y).partition a.τ b (fun n => dot (n f) (n a.o)) / 3 := by
  rw [partition_integrate a.D a.τ b a.y a.start.1 (no_leg_at_start a.start), hU]
  have hfun : (fun n : Plane → Vec3 =>
      siteFunctional .U (fun v => ∏ z ∈ a.D.presentNeighbours a.y, (1 + dot v (n z)))) =
      fun n => 1 + dot (n f) (n a.o) / 3 := by
    funext n
    rw [hN]
    simp only [Finset.prod_pair hne]
    rw [site_U_pair, dot_comm (n a.o) (n f)]
  rw [hfun, partition_affine]

theorem two_partition_after (a : Departure) (hU : a.D.status a.y = .U) (f : Plane)
    (hN : a.D.presentNeighbours a.y = {a.o, f}) (hne : a.o ≠ f) (b : Bool) :
    (traceStep a.D a.y a.o).partition a.τ b (fun _ => 1) =
      (removeSite a.D a.y).partition a.τ b (fun _ => 1) := by
  have hyo : a.y ≠ a.o := by
    have ha := (Finset.mem_filter.mp a.present).1
    have hd := neighbour_adjacent ha
    intro he
    simp [← he, Adjacent, latticeDist] at hd
  have hactive : a.y ∈ (traceStep a.D a.y a.o).active := by
    rw [trace_active a.D a.y a.o hU]
    exact a.start.1
  rw [partition_integrate (traceStep a.D a.y a.o) a.τ b a.y hactive
    (no_leg_at_start a.start)]
  have hfun : (fun n : Plane → Vec3 =>
      siteFunctional ((traceStep a.D a.y a.o).status a.y)
        (fun v => ∏ z ∈ (traceStep a.D a.y a.o).presentNeighbours a.y, (1 + dot v (n z)))) =
      fun _ => 1 := by
    funext n
    rw [trace_neighbours a.D a.y a.o hU hyo, hN]
    rw [Finset.erase_insert (show a.o ∉ ({f} : Finset Plane) by
      simpa only [Finset.mem_singleton] using hne)]
    simp [traceStep, hU, site_D_single]
  rw [hfun, remove_trace_partition a.D a.τ b a.y a.o hU]

/-- The two integrated partitions, proved directly from their finite sums. -/
theorem two_factorization : TwoFactorizationStatement := by
  intro a hU f hN hne b
  refine ⟨?_, two_partition_after a hU f hN hne b⟩
  rw [two_partition_raw a hU f hN hne b]
  unfold responseI₂ removedPairMean Network.expectation
  by_cases hz : (removeSite a.D a.y).partition a.τ b (fun _ => 1) = 0
  · rw [hz, pair_partition_zero (removeSite a.D a.y) a.τ b f a.o hz]
    norm_num
  · field_simp [hz]

/-- The logarithm of the step ratio is meaningful even in a zero-mass fibre. -/
theorem log_stepRatio (a : Departure) (hU : a.D.status a.y = .U) (f : Plane)
    (hN : a.D.presentNeighbours a.y = {a.o, f}) (hne : a.o ≠ f) (b : Bool) :
    Real.log (stepRatio a.D a.τ b a.y a.o) = -Real.log (responseI₂ a.D a.τ b a.y a.o f) := by
  have hF := two_factorization a hU f hN hne b
  unfold stepRatio traceRatio
  change Real.log ((traceStep a.D a.y a.o).partition a.τ b (fun _ => 1) /
    a.D.partition a.τ b (fun _ => 1)) = _
  rw [hF.1, hF.2]
  by_cases hz : (removeSite a.D a.y).partition a.τ b (fun _ => 1) = 0
  · simp [responseI₂, removedPairMean, Network.expectation, hz]
  · have hratio :
        (removeSite a.D a.y).partition a.τ b (fun _ => 1) /
          ((removeSite a.D a.y).partition a.τ b (fun _ => 1) *
            responseI₂ a.D a.τ b a.y a.o f) = (responseI₂ a.D a.τ b a.y a.o f)⁻¹ := by
      field_simp [hz, ne_of_gt (responseI₂_pos a.D a.τ b a.y a.o f)]
    rw [hratio, Real.log_inv]

end AKLT.W.REC017
