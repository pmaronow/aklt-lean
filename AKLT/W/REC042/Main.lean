import AKLT.Blueprint.Rec.NodesWalk
import AKLT.W.REC042.Integration

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC042

/-- The coordinate step needs only the departure restrictions. In particular,
the fixed target can be any distinct site. -/
theorem coordinate_step {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (u v : Plane) (hu : u ∈ D.active) (huS : u ∉ protectedSites G)
    (hstatus : (D.status u = .U ∧ (D.presentNeighbours u).card ≤ 3) ∨
      (D.status u = .D ∧ (D.presentNeighbours u).card ≤ 1))
    (huv : u ≠ v) (k : Fin 3) :
    D.partition τ b (fun m => m u k * m v k) =
      (if D.status u = .U then (1 / 3 : ℝ) else 1 / 5) *
        ∑ o ∈ D.presentNeighbours u,
          (traceStep D u o).partition τ b (fun m => m o k * m v k) := by
  rcases hstatus with ⟨hU, hdeg⟩ | ⟨hD, hdeg⟩
  · rw [ite_eq_left hU]
    calc
      D.partition τ b (fun m => m u k * m v k) =
          (removeSite D u).partition τ b (fun m =>
            siteFunctional (D.status u)
              (fun n => n k * ∏ z ∈ D.presentNeighbours u, (1 + dot n (m z))) * m v k) :=
        partition_coordinate D τ b u v hu huS huv k
      _ = (removeSite D u).partition τ b (fun m =>
          (1 / 3 : ℝ) * ∑ o ∈ D.presentNeighbours u,
            siteFunctional .D
              (fun n => ∏ z ∈ (D.presentNeighbours u).erase o, (1 + dot n (m z))) *
                (m o k * m v k)) := by
        congr 1
        funext m
        rw [hU, siteU_coordinate_finset _ hdeg, mul_assoc, Finset.sum_mul]
        congr 1
        apply Finset.sum_congr rfl
        intro o _
        ring
      _ = (1 / 3 : ℝ) * ∑ o ∈ D.presentNeighbours u,
          (removeSite D u).partition τ b (fun m =>
            siteFunctional .D
              (fun n => ∏ z ∈ (D.presentNeighbours u).erase o, (1 + dot n (m z))) *
                (m o k * m v k)) := by
        rw [AKLT.W.REC002.partition_smul, partition_finset_sum]
      _ = (1 / 3 : ℝ) * ∑ o ∈ D.presentNeighbours u,
          (traceStep D u o).partition τ b (fun m => m o k * m v k) := by
        congr 1
        apply Finset.sum_congr rfl
        intro o ho
        exact (trace_partition_U D τ b u v o hu huS hU huv ho k).symm
  · have hnU : D.status u ≠ .U := by simp [hD]
    rw [ite_eq_right hnU]
    calc
      D.partition τ b (fun m => m u k * m v k) =
          (removeSite D u).partition τ b (fun m =>
            siteFunctional (D.status u)
              (fun n => n k * ∏ z ∈ D.presentNeighbours u, (1 + dot n (m z))) * m v k) :=
        partition_coordinate D τ b u v hu huS huv k
      _ = (removeSite D u).partition τ b (fun m =>
          (1 / 5 : ℝ) * ∑ o ∈ D.presentNeighbours u, m o k * m v k) := by
        congr 1
        funext m
        rw [hD, siteD_coordinate_finset _ hdeg, mul_assoc, Finset.sum_mul]
      _ = (1 / 5 : ℝ) * ∑ o ∈ D.presentNeighbours u,
          (removeSite D u).partition τ b (fun m => m o k * m v k) := by
        rw [AKLT.W.REC002.partition_smul, partition_finset_sum]
      _ = (1 / 5 : ℝ) * ∑ o ∈ D.presentNeighbours u,
          (traceStep D u o).partition τ b (fun m => m o k * m v k) := by
        congr 1
        apply Finset.sum_congr rfl
        intro o _
        exact (trace_partition_removed D u o hnU τ b _).symm

/-- `p:pairwalk`: apply the finite site moment identity to the moving mark. -/
theorem main : AKLT.Blueprint.Rec.CoordinateStepStatement := by
  intro G τ D _ u v hu _ huv b k
  exact coordinate_step D τ b u v hu.1 hu.2.1 hu.2.2 huv k

end AKLT.W.REC042
