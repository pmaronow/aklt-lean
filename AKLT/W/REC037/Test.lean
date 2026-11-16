import AKLT.Blueprint.Rec.NodesWalk
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC037

theorem moment_sum {ι : Type} [Fintype ι] (f : ι → Vec3 → ℝ) :
    moment (fun v => ∑ i, f i v) = ∑ i, moment (f i) := by
  unfold moment
  rw [Finset.sum_comm, Finset.mul_sum]

theorem moment_smul (c : ℝ) (f : Vec3 → ℝ) :
    moment (fun v => c * f v) = c * moment f := by
  unfold moment
  rw [← Finset.mul_sum]
  ring

theorem sum_diag2 (f g : Fin 3 → ℝ) :
    (∑ i : Fin 3, ∑ j : Fin 3, f i * g j * (if i = j then 1 else 0)) =
      ∑ i, f i * g i := by
  apply Finset.sum_congr rfl
  intro i hi
  simp

theorem sum_diag_pair (f g h q : Fin 3 → ℝ) :
    (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
      f i * g j * h k * q l * (if i = j ∧ k = l then 1 else 0)) =
      (∑ i, f i * g i) * (∑ k, h k * q k) := by
  calc
    _ = ∑ i, ∑ j, ∑ k, (if i = j then f i * g j * h k * q k else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      by_cases hij : i = j
      · subst j
        simp
      · simp [hij]
    _ = ∑ i, ∑ k, ∑ j, (if i = j then f i * g j * h k * q k else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_comm
    _ = ∑ i, ∑ k, f i * g i * h k * q k := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro k hk
      simp
    _ = (∑ i, f i * g i) * (∑ k, h k * q k) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring

end AKLT.W.REC037
