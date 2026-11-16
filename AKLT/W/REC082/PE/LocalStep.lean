import AKLT.W.REC082.PE.SetMoments
import AKLT.W.REC082.PE.Iteration

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Rec

namespace AKLT.W.REC082.PE

private theorem paddedSite_const_mul (s : Status) (c : ℝ) (f : Vec3 → ℝ) :
    paddedSiteFunctional s (fun a => c * f a) = c * paddedSiteFunctional s f := by
  simpa only [mul_comm] using paddedSite_mul_const s f c

/-- The marked one-site identity, with the fixed target coordinate retained
as an arbitrary scalar. The X law is a unit atom at zero. -/
private theorem marked_site_step (s : Status) (S : Finset Plane)
    (hs : (s = .U ∧ S.card ≤ 3) ∨ (s = .D ∧ S.card ≤ 1))
    (a : Plane → Vec3) (k : Fin 3) (c : ℝ) :
    paddedSiteFunctional s (fun z => (z k * c) * ∏ o ∈ S, (1 + dot z (a o))) =
      (if s = .U then (1 / 3 : ℝ) else 1 / 5) *
        ∑ o ∈ S, paddedSiteFunctional (if s = .U then .D else .X)
          (fun z => (a o k * c) * ∏ p ∈ S.erase o, (1 + dot z (a p))) := by
  classical
  have hmul (t : Status) :
      paddedSiteFunctional t (fun z => (z k * c) * ∏ o ∈ S, (1 + dot z (a o))) =
        paddedSiteFunctional t (fun z => z k * ∏ o ∈ S, (1 + dot z (a o))) * c := by
    rw [← paddedSite_mul_const]
    congr 1
    funext z
    ring
  rcases hs with ⟨rfl, hS⟩ | ⟨rfl, hS⟩
  · simp only [ite_true, hmul, uMoment_finset S hS a k, paddedSite_const_mul]
    rw [mul_assoc, Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro o ho
    ring
  · simp only [show Status.D ≠ Status.U by decide, ite_false, hmul, dMoment_finset S hS a k,
      paddedSite_X]
    have hzero (o : Plane) : (∏ p ∈ S.erase o, (1 + dot (0 : Vec3) (a p))) = 1 := by
      simp [dot]
    simp only [hzero, mul_one]
    rw [mul_assoc, Finset.sum_mul]

private theorem present_ne {G : Finset Plane} {D : Network G} {u o : Plane}
    (hp : D.Present u o) : o ≠ u := by
  rintro rfl
  simpa [Adjacent, latticeDist] using hp.2.2.1

/-- For every outside configuration the site laws away from the departure
agree before and after the trace step. -/
private theorem outside_weights_step {G : Finset Plane} (D : Network G)
    (u : G) (o : Plane) (n : {x : G // x ≠ u} → SpinLetter) :
    (∏ x : {x : G // x ≠ u}, paddedWeight ((traceStep D u.val o).status x.val.val) (n x)) =
      ∏ x : {x : G // x ≠ u}, paddedWeight (D.status x.val.val) (n x) := by
  apply Finset.prod_congr rfl
  intro x hx
  have hne : x.val.val ≠ u.val := fun he => x.property (Subtype.ext he)
  simp only [traceStep, Function.update_of_ne hne]

/-- Disintegration of each successor numerator using exactly the same
outside configurations and original-leg factors as the pre-step numerator. -/
private theorem successor_partition_fibre {G : Finset Plane} (D : Network G)
    (τ : PinAssignment G) (b : Bool) (u : G) (v o : Plane)
    (hu : D.AdmissibleStart u.val) (hp : D.Present u.val o)
    (huv : u.val ≠ v) (k : Fin 3) :
    (traceStep D u.val o).partition τ b (fun a => a o k * a v k) =
      ∑ n : {x : G // x ≠ u} → SpinLetter,
        (∏ x : {x : G // x ≠ u}, paddedWeight (D.status x.val.val) (n x)) *
          exteriorFactors D τ b u.val (fibreSpins u n) *
            paddedSiteFunctional (if D.status u.val = .U then .D else .X)
              (fun a => (fibreSpins u n o k * fibreSpins u n v k) *
                ∏ p ∈ (D.presentNeighbours u.val).erase o,
                  (1 + dot a (fibreSpins u n p))) := by
  classical
  rw [partition_site_fibre _ τ b u hu.2.1]
  apply Finset.sum_congr rfl
  intro n hn
  rw [outside_weights_step, exteriorFactors_step hu hp, departureNeighbours_step hu hp]
  have ho : o ≠ u.val := present_ne hp
  simp only [traceStep, Function.update_self,
    Function.update_of_ne ho, Function.update_of_ne huv.symm]

/-- Local coordinate contraction proved inside the original finite
partition, for both pin choices and with all original legs retained. -/
theorem coordinateStep : CoordinateStepStatement := by
  intro G τ D hD u v hu hv huv b k
  classical
  let uG : G := ⟨u, (Finset.mem_filter.mp hu.1).1⟩
  have hsucc (o : Plane) (ho : o ∈ D.presentNeighbours u) :=
    successor_partition_fibre D τ b uG v o hu (Finset.mem_filter.mp ho).2 huv k
  rw [partition_site_fibre D τ b uG hu.2.1]
  simp only [uG, Function.update_self, Function.update_of_ne huv.symm]
  simp_rw [marked_site_step (D.status u) (D.presentNeighbours u) hu.2.2]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro o ho
  rw [hsucc o ho, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  dsimp only [uG]
  ring

end AKLT.W.REC082.PE
