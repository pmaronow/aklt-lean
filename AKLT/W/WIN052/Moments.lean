module
public import AKLT.W.WIN052.Geometry

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Win

namespace AKLT.W.WIN052

theorem moment_sum {ι : Type} [Fintype ι] (f : ι → Vec3 → ℝ) :
    moment (fun v => ∑ i, f i v) = ∑ i, moment (f i) := by
  unfold moment
  rw [Finset.sum_comm, Finset.mul_sum]

theorem moment_scale (c : ℝ) (f : Vec3 → ℝ) :
    moment (fun v => c * f v) = c * moment f := by
  unfold moment
  rw [← Finset.mul_sum]
  ring

theorem moment_add (f g : Vec3 → ℝ) :
    moment (fun v => f v + g v) = moment f + moment g := by
  simp [moment, Finset.sum_add_distrib, mul_add]

theorem moment_const (hM : AKLT.Blueprint.Top.MomentsStatement) (c : ℝ) :
    moment (fun _ => c) = c := by
  simpa only [mul_one, hM.2.2.2.1] using moment_scale c (fun _ => 1)

theorem moment_dot (hM : AKLT.Blueprint.Top.MomentsStatement) (a : Vec3) :
    moment (fun v => dot v a) = 0 := by
  have hexp : ∀ v : Vec3, dot v a = ∑ i : Fin 3, a i * v i := by
    intro v
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  simp_rw [hexp, moment_sum, moment_scale, hM.2.2.2.2.1]
  simp

theorem pairMoment_of_moments (hM : AKLT.Blueprint.Top.MomentsStatement)
    (a b : Vec3) : moment (fun v => dot v a * dot v b) = (1 / 3 : ℝ) * dot a b := by
  rcases hM with ⟨_, _, _, _, _, _, hSecond, _, _, _⟩
  have hexp : ∀ v : Vec3, dot v a * dot v b =
      ∑ i : Fin 3, ∑ j : Fin 3, (a j * b i) * (v j * v i) := by
    intro v
    simp only [dot, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [hexp, moment_sum, moment_scale, hSecond]
  simp [Fin.sum_univ_succ, dot]
  ring

theorem tripleMoment (hM : AKLT.Blueprint.Top.MomentsStatement) (a b c : Vec3) :
    moment (fun v => dot v a * dot v b * dot v c) = 0 := by
  have hexp : ∀ v : Vec3, dot v a * dot v b * dot v c =
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
        (a k * b j * c i) * (v k * v j * v i) := by
    intro v
    simp only [dot, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  simp_rw [hexp, moment_sum, moment_scale, hM.2.2.2.2.2.1]
  simp

theorem fourthMoment (hM : AKLT.Blueprint.Top.MomentsStatement) (a b c d : Vec3) :
    moment (fun v => dot v a * dot v b * dot v c * dot v d) =
      (dot a b * dot c d + dot a c * dot b d + dot a d * dot b c) / 15 := by
  have hexp : ∀ v : Vec3, dot v a * dot v b * dot v c * dot v d =
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
        (a l * b k * c j * d i) * (v l * v k * v j * v i) := by
    intro v
    simp only [dot, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring
  simp_rw [hexp, moment_sum, moment_scale, hM.2.2.2.2.2.2.2.1]
  norm_num [Fin.sum_univ_succ, dot]
  ring

theorem fourFactors (hM : AKLT.Blueprint.Top.MomentsStatement) (a b c d : Vec3) :
    moment (fun v => (1 + dot v a) * (1 + dot v b) * (1 + dot v c) *
      (1 + dot v d)) =
    1 + (dot a b + dot a c + dot a d + dot b c + dot b d + dot c d) / 3 +
      (dot a b * dot c d + dot a c * dot b d + dot a d * dot b c) / 15 := by
  have hexp : ∀ v : Vec3,
      (1 + dot v a) * (1 + dot v b) * (1 + dot v c) * (1 + dot v d) =
      1 + dot v a + dot v b + dot v c + dot v d +
      dot v a * dot v b + dot v a * dot v c + dot v a * dot v d +
      dot v b * dot v c + dot v b * dot v d + dot v c * dot v d +
      dot v a * dot v b * dot v c + dot v a * dot v b * dot v d +
      dot v a * dot v c * dot v d + dot v b * dot v c * dot v d +
      dot v a * dot v b * dot v c * dot v d := by
    intro v
    ring
  simp_rw [hexp, moment_add, moment_const hM, moment_dot hM,
    pairMoment_of_moments hM, tripleMoment hM, fourthMoment hM]
  ring

@[simp] theorem dot_zero (a : Vec3) : dot a 0 = 0 := by simp [dot]
@[simp] theorem zero_dot (a : Vec3) : dot 0 a = 0 := by simp [dot]

end AKLT.W.WIN052
