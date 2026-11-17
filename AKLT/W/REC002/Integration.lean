import AKLT.W.REC002.Bonds

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC002

theorem spinSum_status (V : Finset Plane) (s t : Plane → Status)
    (hst : ∀ x ∈ V, s x = t x) (F : (Plane → Vec3) → ℝ) :
    spinSum V s F = spinSum V t F := by
  unfold spinSum
  apply Finset.sum_congr rfl
  intro n _
  congr 1
  apply Finset.prod_congr rfl
  intro x _
  rw [hst x x.property]

theorem site_constants (s : Status) (A B : ℝ) (f : Vec3 → ℝ) :
    siteFunctional s (fun v => A * f v * B) = A * siteFunctional s f * B := by
  unfold siteFunctional
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem partition_integrate {G : Finset Plane} (D : Network G) (y : Plane)
    (hy : y ∈ D.active) (hleg : ∀ e : originalLegs G, e.val.1 ≠ y)
    (τ : PinAssignment G) (b : Bool) :
    D.partition τ b (fun _ => 1) =
      (removeSite D y).partition τ b
        (fun n => siteFunctional (D.status y)
          (fun v => ∏ z ∈ D.presentNeighbours y, (1 + dot v (n z)))) := by
  let E := removeSite D y
  let F := fun n => bondProduct D.bonds n * legProduct D.active τ b n
  have hnot : y ∉ E.active := by simp [E, mem_remove_active]
  have hactive : D.active = insert y E.active := by
    simp only [E, remove_active, Finset.insert_erase hy]
  have hstatus : ∀ x ∈ E.active, D.status x = E.status x := by
    intro x hx
    have hn := (mem_remove_active D y x).mp hx
    simp [E, removeSite, Function.update_of_ne hn.2]
  calc
    D.partition τ b (fun _ => 1) = spinSum (insert y E.active) D.status F := by
      rw [← hactive, partition_spinSum]
      simp only [F, one_mul]
    _ = ∑ n : E.active → SpinLetter, (∏ x : E.active, spinWeight (D.status x) (n x)) *
        siteFunctional (D.status y) (fun v => F (Function.update (extend E.active n) y v)) :=
      spinSum_insert E.active y hnot D.status F
    _ = spinSum E.active D.status
        (fun n => siteFunctional (D.status y)
          (fun v => ∏ z ∈ D.presentNeighbours y, (1 + dot v (n z))) *
            bondProduct E.bonds n * legProduct E.active τ b n) := by
      unfold spinSum
      apply Finset.sum_congr rfl
      intro n _
      dsimp [F]
      simp_rw [bondProduct_remove D y, legProduct_remove D y τ b hleg]
      rw [site_constants]
      ring
    _ = E.partition τ b
        (fun n => siteFunctional (D.status y)
          (fun v => ∏ z ∈ D.presentNeighbours y, (1 + dot v (n z)))) := by
      rw [partition_spinSum, ← spinSum_status E.active D.status E.status hstatus]

def configWeight {G : Finset Plane} (D : Network G) (τ : PinAssignment G) (b : Bool)
    (n : D.active → SpinLetter) : ℝ :=
  (∏ x : D.active, spinWeight (D.status x) (n x)) *
    bondProduct D.bonds (D.spins n) * legProduct D.active τ b (D.spins n)

theorem partition_weight {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (f : (Plane → Vec3) → ℝ) :
    D.partition τ b f = ∑ n, configWeight D τ b n * f (D.spins n) := by
  unfold Network.partition configWeight bondProduct legProduct
  apply Finset.sum_congr rfl
  intro n _
  ring

theorem spins_ball {G : Finset Plane} (D : Network G) (n : D.active → SpinLetter)
    (x : Plane) : normSq (D.spins n x) ≤ 1 := by
  unfold Network.spins
  split_ifs
  · exact spin_ball _
  · norm_num [normSq, dot]

theorem configWeight_nonneg {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (n : D.active → SpinLetter) : 0 ≤ configWeight D τ b n := by
  unfold configWeight
  apply mul_nonneg
  · apply mul_nonneg
    · apply Finset.prod_nonneg
      intro x _
      cases hs : D.status x <;> cases hj : n x <;> norm_num [spinWeight, hs, hj]
    · apply Finset.prod_nonneg
      intro e _
      exact factor_nonneg _ _ (spins_ball D n e.1) (spins_ball D n e.2)
  · apply Finset.prod_nonneg
    intro e _
    split_ifs
    · exact factor_nonneg _ _ (le_of_eq (τ e).property) (spins_ball D n e.val.1)
    · norm_num

theorem partition_zero {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (hzero : D.partition τ b (fun _ => 1) = 0)
    (f : (Plane → Vec3) → ℝ) : D.partition τ b f = 0 := by
  have hs : ∑ n, configWeight D τ b n = 0 := by
    simpa only [partition_weight, mul_one] using hzero
  have hw : ∀ n, configWeight D τ b n = 0 := by
    intro n
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun n _ => configWeight_nonneg D τ b n)).mp hs n (Finset.mem_univ _)
  simp only [partition_weight, hw, zero_mul, Finset.sum_const_zero]

theorem partition_expectation {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (f : (Plane → Vec3) → ℝ) :
    D.partition τ b (fun _ => 1) * D.expectation τ b f = D.partition τ b f := by
  unfold Network.expectation
  by_cases h : D.partition τ b (fun _ => 1) = 0
  · rw [h, zero_mul, partition_zero D τ b h f]
  · exact mul_div_cancel₀ _ h

theorem partition_add {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (f g : (Plane → Vec3) → ℝ) :
    D.partition τ b (fun n => f n + g n) = D.partition τ b f + D.partition τ b g := by
  simp only [partition_weight, mul_add, Finset.sum_add_distrib]

theorem partition_smul {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (c : ℝ) (f : (Plane → Vec3) → ℝ) :
    D.partition τ b (fun n => c * f n) = c * D.partition τ b f := by
  simp only [partition_weight, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  ring

end AKLT.W.REC002
