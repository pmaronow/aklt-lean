module
public import AKLT.W.REC017.Quadrature

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC017

def networkWeight {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (n : D.active → SpinLetter) : ℝ :=
  (∏ x : D.active, spinWeight (D.status x.val) (n x)) *
    (∏ e ∈ D.bonds, (1 + dot (D.spins n e.1) (D.spins n e.2))) *
    ∏ e : originalLegs G,
      if b = true ∧ e.val.1 ∈ D.active then 1 + dot (τ e).val (D.spins n e.val.1) else 1

theorem partition_weight {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (F : (Plane → Vec3) → ℝ) :
    D.partition τ b F = ∑ n, networkWeight D τ b n * F (D.spins n) := by
  unfold Network.partition networkWeight
  apply Finset.sum_congr rfl
  intro n hn
  ring

theorem spins_ball {G : Finset Plane} (D : Network G) (n : D.active → SpinLetter)
    (x : Plane) : normSq (D.spins n x) ≤ 1 := by
  by_cases hx : x ∈ D.active
  · simpa [Network.spins, hx] using spin_ball (n ⟨x, hx⟩)
  · simp [Network.spins, hx, normSq, dot]

theorem networkWeight_nonneg {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (n : D.active → SpinLetter) : 0 ≤ networkWeight D τ b n := by
  unfold networkWeight
  apply mul_nonneg
  · apply mul_nonneg
    · exact Finset.prod_nonneg fun x _ => weight_nonneg _ _
    · apply Finset.prod_nonneg
      intro e he
      have h := (dot_bounds (spins_ball D n e.1) (spins_ball D n e.2)).1
      linarith
  · apply Finset.prod_nonneg
    intro e he
    split_ifs
    · have h := (dot_bounds (τ e).property.le (spins_ball D n e.val.1)).1
      linarith
    · norm_num

theorem partition_mono {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) {F H : (Plane → Vec3) → ℝ}
    (h : ∀ n : D.active → SpinLetter, F (D.spins n) ≤ H (D.spins n)) :
    D.partition τ b F ≤ D.partition τ b H := by
  simp only [partition_weight]
  exact Finset.sum_le_sum fun n _ => mul_le_mul_of_nonneg_left (h n)
    (networkWeight_nonneg D τ b n)

theorem partition_nonneg {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) : 0 ≤ D.partition τ b (fun _ => 1) := by
  rw [partition_weight]
  exact Finset.sum_nonneg fun n _ => mul_nonneg (networkWeight_nonneg D τ b n) (by norm_num)

theorem partition_affine {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (F : (Plane → Vec3) → ℝ) :
    D.partition τ b (fun n => 1 + F n / 3) =
      D.partition τ b (fun _ => 1) + D.partition τ b F / 3 := by
  simp only [partition_weight]
  rw [Finset.sum_div, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  ring

theorem pair_partition_bounds {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (x z : Plane) :
    -D.partition τ b (fun _ => 1) ≤ D.partition τ b (fun n => dot (n x) (n z)) ∧
    D.partition τ b (fun n => dot (n x) (n z)) ≤ D.partition τ b (fun _ => 1) := by
  constructor
  · have h := partition_mono D τ b (F := fun _ => -1) (H := fun n => dot (n x) (n z))
      (fun n => (dot_bounds (spins_ball D n x) (spins_ball D n z)).1)
    simpa only [partition_weight, mul_neg_one, mul_one, Finset.sum_neg_distrib] using h
  · exact partition_mono D τ b (fun n => (dot_bounds (spins_ball D n x) (spins_ball D n z)).2)

theorem pair_partition_zero {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (x z : Plane) (h : D.partition τ b (fun _ => 1) = 0) :
    D.partition τ b (fun n => dot (n x) (n z)) = 0 := by
  have hp := pair_partition_bounds D τ b x z
  rw [h] at hp
  linarith [hp.1, hp.2]

theorem pair_expectation_bounds {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (x z : Plane) :
    -1 ≤ D.expectation τ b (fun n => dot (n x) (n z)) ∧
      D.expectation τ b (fun n => dot (n x) (n z)) ≤ 1 := by
  have hp := pair_partition_bounds D τ b x z
  have hn := partition_nonneg D τ b
  by_cases hz : D.partition τ b (fun _ => 1) = 0
  · simp [Network.expectation, hz]
  · have hzpos : 0 < D.partition τ b (fun _ => 1) := lt_of_le_of_ne hn (Ne.symm hz)
    unfold Network.expectation
    constructor
    · exact (le_div_iff₀ hzpos).mpr (by simpa using hp.1)
    · exact (div_le_iff₀ hzpos).mpr (by simpa using hp.2)

theorem responseI₂_pos {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (y o f : Plane) : 0 < AKLT.Blueprint.Rec.responseI₂ D τ b y o f := by
  have h := (pair_expectation_bounds (removeSite D y) τ b f o).1
  unfold AKLT.Blueprint.Rec.responseI₂ removedPairMean
  linarith

end AKLT.W.REC017
