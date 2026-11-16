import AKLT.Blueprint.Q.NodesFrames

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Challenge

namespace AKLT.W.Q005

lemma phi_pos : 0 < goldenRatio := by
  unfold goldenRatio
  positivity

lemma phi_sq : goldenRatio ^ 2 = goldenRatio + 1 := by
  unfold goldenRatio
  have hs : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  nlinarith

lemma radius_pos : 0 < icoRadius := by
  unfold icoRadius
  apply Real.sqrt_pos.2
  have := phi_pos
  linarith

lemma radius_sq : icoRadius ^ 2 = goldenRatio + 2 := by
  unfold icoRadius
  have h : 0 ≤ goldenRatio + 2 := by have := phi_pos; linarith
  rw [Real.sq_sqrt h]

lemma bound_alt : frameBound = 2 / (101 * (goldenRatio + 2)) := by
  unfold frameBound goldenRatio
  have hs : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  field_simp
  nlinarith

lemma dot_coord (u v : Vec3) : dot u v = u 0 * v 0 + u 1 * v 1 + u 2 * v 2 := by
  simp [dot, Fin.sum_univ_succ]
  ring

lemma rot_one_coords (u : Vec3) :
    frameRotation.mulVec u 0 = (99 / 101 : ℝ) * u 0 - (20 / 101 : ℝ) * u 1 ∧
    frameRotation.mulVec u 1 = (20 / 101 : ℝ) * u 0 + (99 / 101 : ℝ) * u 1 ∧
    frameRotation.mulVec u 2 = u 2 := by
  norm_num [frameRotation, Matrix.mulVec, Matrix.mul_apply, dotProduct, Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail] ; ring

lemma rot_sq_coords (u : Vec3) :
    (frameRotation ^ 2).mulVec u 0 = (9401 / 10201 : ℝ) * u 0 - (3960 / 10201 : ℝ) * u 1 ∧
    (frameRotation ^ 2).mulVec u 1 = (3960 / 10201 : ℝ) * u 0 + (9401 / 10201 : ℝ) * u 1 ∧
    (frameRotation ^ 2).mulVec u 2 = u 2 := by
  norm_num [frameRotation, pow_two, Matrix.mulVec, Matrix.mul_apply, dotProduct, Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail] ; ring

lemma gap_one (u : Vec3) (hu : normSq u = 1) :
    1 - dot u (frameRotation.mulVec u) = (2 / 101 : ℝ) * (u 0 ^ 2 + u 1 ^ 2) := by
  obtain ⟨h0,h1,h2⟩ := rot_one_coords u
  rw [dot_coord, h0,h1,h2]
  have hn : u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 = 1 := by
    have hx : u 0 * u 0 + u 1 * u 1 + u 2 * u 2 = 1 := by simpa [normSq, dot_coord] using hu
    nlinarith [hx]
  rw [← hn]
  ring

lemma gap_two (u : Vec3) (hu : normSq u = 1) :
    1 - dot u ((frameRotation ^ 2).mulVec u) = (800 / 10201 : ℝ) * (u 0 ^ 2 + u 1 ^ 2) := by
  obtain ⟨h0,h1,h2⟩ := rot_sq_coords u
  rw [dot_coord, h0,h1,h2]
  have hn : u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 = 1 := by
    have hx : u 0 * u 0 + u 1 * u 1 + u 2 * u 2 = 1 := by simpa [normSq, dot_coord] using hu
    nlinarith [hx]
  rw [← hn]
  ring

lemma planarSq_lower (a : IcoLetter) :
    1 / (goldenRatio + 2) ≤ (icoVector a 0)^2 + (icoVector a 1)^2 := by
  have hp := phi_pos
  have hr := radius_pos
  have hrsq := radius_sq
  have hphi := phi_sq
  rcases a with ⟨j, s, t⟩
  fin_cases j <;> fin_cases s <;> fin_cases t <;>
    simp [icoVector, signValue] <;>
    field_simp [icoRadius] <;>
    first | rfl | exact le_rfl | exact le_rfl | nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 5 by norm_num)]

lemma gap_factor_one_eq : frameBound = (2 / 101) / (goldenRatio + 2) := by
  rw [bound_alt]
  field_simp

lemma gap_factor_two_le : (2 / (101 * (goldenRatio + 2))) ≤ (800 / 10201) / (goldenRatio + 2) := by
  have hp : 0 < goldenRatio + 2 := by have := phi_pos; linarith
  calc
    2 / (101 * (goldenRatio + 2)) = (2 / 101) / (goldenRatio + 2) := by field_simp
    _ ≤ (800 / 10201) / (goldenRatio + 2) :=
      (div_le_div_iff_of_pos_right hp).2 (by norm_num)

lemma witnessPlanar :
    (icoVector (0, 0, 0) 0)^2 + (icoVector (0, 0, 0) 1)^2 = 1 / (goldenRatio + 2) := by
  simp [icoVector, signValue]
  rw [← radius_sq]

lemma ico_norm (a : IcoLetter) : normSq (icoVector a) = 1 := by
  rcases a with ⟨j,s,t⟩
  fin_cases j <;> fin_cases s <;> fin_cases t <;>
    simp [normSq, dot_coord, icoVector, signValue] <;>
    field_simp [radius_pos.ne'] <;>
    rw [radius_sq] <;>
    nlinarith [phi_sq]

end AKLT.W.Q005

namespace AKLT.W.Q005

theorem main : AKLT.Blueprint.Q.SelfRotationStatement := by
  constructor
  · intro k hk1 hk2 a
    have hk : k = 1 ∨ k = 2 := by omega
    rcases hk with rfl | rfl
    · simp only [pow_one]
      change frameBound ≤ 1 - dot (icoVector a) (frameRotation.mulVec (icoVector a))
      rw [gap_one (icoVector a) (ico_norm a)]
      calc
        frameBound = (2 / 101) / (goldenRatio + 2) := gap_factor_one_eq
        _ ≤ (2 / 101) * ((icoVector a 0)^2 + (icoVector a 1)^2) := by
          calc
            (2 / 101) / (goldenRatio + 2) = (2 / 101) * (1 / (goldenRatio + 2)) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left (planarSq_lower a) (by norm_num)
    · change frameBound ≤ 1 - dot (icoVector a) ((frameRotation ^ 2).mulVec (icoVector a))
      rw [gap_two (icoVector a) (ico_norm a)]
      calc
        frameBound = 2 / (101 * (goldenRatio + 2)) := bound_alt
        _ ≤ (800 / 10201) / (goldenRatio + 2) := gap_factor_two_le
        _ ≤ (800 / 10201) * ((icoVector a 0)^2 + (icoVector a 1)^2) := by
          calc
            (800 / 10201) / (goldenRatio + 2) = (800 / 10201) * (1 / (goldenRatio + 2)) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left (planarSq_lower a) (by norm_num)
  · have hu : normSq (icoVector (0, 0, 0)) = 1 := ico_norm (0, 0, 0)
    have hg := gap_one (icoVector (0, 0, 0)) hu
    change 1 - dot (frameVector 0 (0,0,0)) (frameVector 1 (0,0,0)) = frameBound
    simpa [frameVector] using (calc
      1 - dot (icoVector (0,0,0)) (frameRotation.mulVec (icoVector (0,0,0))) =
          (2 / 101) * ((icoVector (0,0,0) 0)^2 + (icoVector (0,0,0) 1)^2) := hg
      _ = frameBound := by rw [witnessPlanar, bound_alt]; field_simp)

end AKLT.W.Q005
