module
public import AKLT.Blueprint.Mom.NodesMean

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.MOM024

private theorem weighted_sq_mean_le {α : Type} [Fintype α]
    (q x : α → ℝ) (hq : ∀ a, 0 ≤ q a) (hsum : (∑ a, q a) = 1) :
    (∑ a, q a * x a) ^ 2 ≤ ∑ a, q a * (x a) ^ 2 := by
  let m : ℝ := ∑ a, q a * x a
  have hvar : 0 ≤ ∑ a, q a * (x a - m) ^ 2 :=
    Finset.sum_nonneg fun a _ => mul_nonneg (hq a) (sq_nonneg (x a - m))
  have hiden : (∑ a, q a * (x a - m) ^ 2) =
      (∑ a, q a * x a ^ 2) - m ^ 2 := by
    have hmid : (∑ a, (2 * m) * (q a * x a)) =
        (2 * m) * (∑ a, q a * x a) := by
      exact (Finset.mul_sum Finset.univ (fun a => q a * x a) (2 * m)).symm
    have hlast : (∑ a, q a * m ^ 2) = (∑ a, q a) * m ^ 2 := by
      exact (Finset.sum_mul Finset.univ (fun a => q a) (m ^ 2)).symm
    calc
      (∑ a, q a * (x a - m) ^ 2) =
          ∑ a, (q a * x a ^ 2 - (2 * m) * (q a * x a) + q a * m ^ 2) := by
            apply Finset.sum_congr rfl
            intro a _
            ring
      _ = (∑ a, q a * x a ^ 2) - (∑ a, (2 * m) * (q a * x a)) +
          (∑ a, q a * m ^ 2) := by rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      _ = (∑ a, q a * x a ^ 2) - m ^ 2 := by rw [hmid, hlast, hsum]; dsimp [m]; ring
  rw [hiden] at hvar
  dsimp [m] at hvar
  linarith

theorem main : AKLT.Blueprint.Mom.PositiveMixtureEstimateStatement := by
  intro α hα t A B r hr ht htsum hA hB
  classical
  let Z : ℝ := ∑ η, t η * A η
  have hZlow : 1 / 2 ≤ Z := by
    dsimp [Z]
    calc
      (1 / 2 : ℝ) = (∑ η, t η) * (1 / 2) := by rw [htsum]; ring
      _ = ∑ η, t η * (1 / 2) := by rw [Finset.sum_mul]
      _ ≤ ∑ η, t η * A η := Finset.sum_le_sum fun η _ =>
        mul_le_mul_of_nonneg_left (hA η) (ht η)
  have hZpos : 0 < Z := lt_of_lt_of_le (by norm_num) hZlow
  have hZne : Z ≠ 0 := ne_of_gt hZpos
  let q : α → ℝ := fun η => (t η * A η) / Z
  have hq : ∀ η, 0 ≤ q η := by
    intro η
    dsimp [q]
    exact div_nonneg (mul_nonneg (ht η) (le_trans (by norm_num : (0 : ℝ) ≤ 1 / 2) (hA η))) hZpos.le
  have hqsum : (∑ η, q η) = 1 := by
    calc
      (∑ η, q η) = (∑ η, t η * A η) / Z := by
        simp [q, div_eq_mul_inv, ← Finset.sum_mul]
      _ = 1 := by
        simp [Z, hZne]
  have hApos : ∀ η, 0 < A η := fun η => lt_of_lt_of_le (by norm_num) (hA η)
  have hratio (i : Fin 3) :
      (∑ η, t η * B η i) / Z = ∑ η, q η * (B η i / A η) := by
    calc
      (∑ η, t η * B η i) / Z = ∑ η, (t η * B η i) / Z := by
        simp [div_eq_mul_inv, ← Finset.sum_mul]
      _ = ∑ η, q η * (B η i / A η) := by
        apply Finset.sum_congr rfl
        intro η _
        dsimp [q]
        field_simp [hZne, ne_of_gt (hApos η)]
  have hcoords :
      ∑ i : Fin 3, ((∑ η, q η * (B η i / A η)) ^ 2) ≤
        ∑ i : Fin 3, ∑ η, q η * (B η i / A η) ^ 2 := by
    apply Finset.sum_le_sum
    intro i hi
    exact weighted_sq_mean_le q (fun η => B η i / A η) hq hqsum
  have hswap :
      (∑ i : Fin 3, ∑ η, q η * (B η i / A η) ^ 2) =
        ∑ η, q η * normSq (fun i => B η i / A η) := by
    rw [Finset.sum_comm]
    simp [normSq, dot, pow_two, Finset.mul_sum]
  have hweighted :
      (∑ η, q η * normSq (fun i => B η i / A η)) ≤ r ^ 2 := by
    calc
      (∑ η, q η * normSq (fun i => B η i / A η)) ≤ ∑ η, q η * r ^ 2 :=
        Finset.sum_le_sum fun η _ => mul_le_mul_of_nonneg_left (hB η) (hq η)
      _ = r ^ 2 := by rw [← Finset.sum_mul, hqsum]; ring
  constructor
  · exact hZlow
  · change normSq (fun i => (∑ η, t η * B η i) / Z) ≤ r ^ 2
    calc
      normSq (fun i => (∑ η, t η * B η i) / Z) =
          ∑ i : Fin 3, ((∑ η, q η * (B η i / A η)) ^ 2) := by
            simp [normSq, dot, hratio, pow_two]
      _ ≤ ∑ i : Fin 3, ∑ η, q η * (B η i / A η) ^ 2 := hcoords
      _ = ∑ η, q η * normSq (fun i => B η i / A η) := hswap
      _ ≤ r ^ 2 := hweighted

#print axioms main

end AKLT.W.MOM024
