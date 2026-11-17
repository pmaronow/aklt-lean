module
public import AKLT.W.REC091.Departure
public import AKLT.W.REC091.Integrals

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Rec

namespace AKLT.W.REC091

theorem partition_affine_one {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (F : (Plane → Vec3) → ℝ) (q : ℝ) :
    D.partition τ b (fun n => 1 + F n / q) =
      D.partition τ b (fun _ => 1) * (1 + D.expectation τ b F / q) := by
  by_cases hq : q = 0
  · simp [hq]
  have hp : (∑ n, networkWeight D τ b n) ≠ 0 := by
    simpa only [partition_eq_sum_weight, mul_one] using (network_partition_pos D τ b).ne'
  simp only [Network.expectation, partition_eq_sum_weight, mul_add, ← mul_div_assoc,
    mul_one, Finset.sum_add_distrib, ← Finset.sum_div]
  field_simp [hp, hq]

theorem partition_affine_three {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (F H K : (Plane → Vec3) → ℝ) :
    D.partition τ b (fun n => 1 + (F n + H n + K n) / 3) =
      D.partition τ b (fun _ => 1) *
        (1 + (D.expectation τ b F + D.expectation τ b H + D.expectation τ b K) / 3) := by
  have hp : (∑ n, networkWeight D τ b n) ≠ 0 := by
    simpa only [partition_eq_sum_weight, mul_one] using (network_partition_pos D τ b).ne'
  simp only [Network.expectation, partition_eq_sum_weight, mul_add, ← mul_div_assoc,
    mul_one, Finset.sum_add_distrib, ← Finset.sum_div]
  field_simp [hp]

theorem twoFactorization : TwoFactorizationStatement := by
  intro a hU f hneigh hne b
  obtain ⟨hcur, hnext⟩ := departure_disintegration a hU b
  constructor
  · rw [hcur]
    have hfun : (fun n : Plane → Vec3 => siteFunctional .U
        (fun v => ∏ z ∈ a.D.presentNeighbors a.y, (1 + dot v (n z)))) =
        (fun n => 1 + dot (n f) (n a.o) / 3) := by
      funext n
      rw [hneigh]
      calc
        _ = siteFunctional .U (fun v => (1 + dot v (n f)) * (1 + dot v (n a.o))) := by
          congr 1
          funext v
          simp [hne, mul_comm]
        _ = _ := integrate_U_two _ _
    rw [hfun, partition_affine_one]
    rfl
  · rw [hnext]
    congr 1
    funext n
    simp [hneigh, hne, integrate_D_one]

theorem threeFactorization : ThreeFactorizationStatement := by
  intro a hU f g hneigh hof hog hfg b
  obtain ⟨hcur, hnext⟩ := departure_disintegration a hU b
  constructor
  · rw [hcur]
    have hfun : (fun n : Plane → Vec3 => siteFunctional .U
        (fun v => ∏ z ∈ a.D.presentNeighbors a.y, (1 + dot v (n z)))) =
        (fun n => 1 + (dot (n f) (n g) + dot (n f) (n a.o) + dot (n g) (n a.o)) / 3) := by
      funext n
      rw [hneigh]
      calc
        _ = siteFunctional .U (fun v =>
            (1 + dot v (n f)) * (1 + dot v (n g)) * (1 + dot v (n a.o))) := by
          congr 1
          funext v
          simp [hof, hog, hfg]
          ring
        _ = _ := integrate_U_three _ _ _
    rw [hfun, partition_affine_three]
    rfl
  · rw [hnext]
    have hfun : (fun n : Plane → Vec3 => siteFunctional .D
        (fun v => ∏ z ∈ (a.D.presentNeighbors a.y).erase a.o, (1 + dot v (n z)))) =
        (fun n => 1 + dot (n f) (n g) / 5) := by
      funext n
      simpa [hneigh, hof, hog, hfg, Ne.symm hof, Ne.symm hog] using
        integrate_D_two (n f) (n g)
    rw [hfun, partition_affine_one]
    rfl

theorem stepRatio_two (a : Departure) (hU : a.D.status a.y = .U)
    (f : Plane) (hn : a.D.presentNeighbors a.y = {a.o, f}) (hne : a.o ≠ f) (b : Bool) :
    stepRatio a.D a.τ b a.y a.o = (responseI₂ a.D a.τ b a.y a.o f)⁻¹ := by
  obtain ⟨hc, hnxt⟩ := twoFactorization a hU f hn hne b
  unfold stepRatio traceRatio
  change (traceStep a.D a.y a.o).partition a.τ b (fun _ => 1) /
      a.D.partition a.τ b (fun _ => 1) = _
  rw [hc, hnxt]
  have hp := (network_partition_pos (removeSite a.D a.y) a.τ b).ne'
  simpa only [mul_one, one_div] using
    (mul_div_mul_left (1 : ℝ) (responseI₂ a.D a.τ b a.y a.o f) hp)

theorem stepRatio_three (a : Departure) (hU : a.D.status a.y = .U)
    (f g : Plane) (hn : a.D.presentNeighbors a.y = {a.o, f, g})
    (hof : a.o ≠ f) (hog : a.o ≠ g) (hfg : f ≠ g) (b : Bool) :
    stepRatio a.D a.τ b a.y a.o =
      responseJ a.D a.τ b a.y f g / responseI a.D a.τ b a.y a.o f g := by
  obtain ⟨hc, hnxt⟩ := threeFactorization a hU f g hn hof hog hfg b
  unfold stepRatio traceRatio
  change (traceStep a.D a.y a.o).partition a.τ b (fun _ => 1) /
      a.D.partition a.τ b (fun _ => 1) = _
  rw [hc, hnxt]
  exact mul_div_mul_left _ _ (network_partition_pos (removeSite a.D a.y) a.τ b).ne'

end AKLT.W.REC091
