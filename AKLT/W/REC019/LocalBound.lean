import AKLT.W.REC019.ThreeMean

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC019

def tripleMeanU (a b c : Vec3) : Vec3 :=
  fun i => moment (fun n => n i * threeProduct a b c n) / moment (threeProduct a b c)

private theorem tripleV_norm (a b c : Vec3) :
    normSq (tripleV a b c) =
      (5 + dot b c)^2 * normSq a + (5 + dot a c)^2 * normSq b +
        (5 + dot a b)^2 * normSq c +
      2 * ((5 + dot b c) * (5 + dot a c) * dot a b +
        (5 + dot b c) * (5 + dot a b) * dot a c +
        (5 + dot a c) * (5 + dot a b) * dot b c) := by
  simp [tripleV, normSq, dot, Fin.sum_univ_three]
  ring

private theorem tripleP_lower_unit {a b c : Vec3}
    (ha : normSq a = 1) (hb : normSq b = 1) (hc : normSq c = 1) :
    -(3 / 2 : ℝ) ≤ tripleP a b c := by
  have he : normSq (a + b + c) = normSq a + normSq b + normSq c +
      2 * tripleP a b c := by
    simp [tripleP, normSq, dot, Fin.sum_univ_three]
    ring
  have hn := normSq_nonnegative (a + b + c)
  rw [he, ha, hb, hc] at hn
  linarith

private theorem norm_div (a : Vec3) (d : ℝ) :
    normSq (fun i => a i / d) = normSq a / d^2 := by
  simp only [normSq, dot, div_mul_div_comm, ← Finset.sum_div, pow_two]

private theorem tripleMeanU_formula {a b c : Vec3} (hp : 0 < 3 + tripleP a b c) :
    tripleMeanU a b c = fun i => tripleV a b c i / (5 * (3 + tripleP a b c)) := by
  funext i
  simp only [tripleMeanU, moment_coord_threeProduct, moment_threeProduct]
  field_simp; ring

theorem three_unit_mean_bound {a b c : Vec3}
    (ha : normSq a = 1) (hb : normSq b = 1) (hc : normSq c = 1) :
    1 / 2 ≤ moment (threeProduct a b c) ∧ normSq (tripleMeanU a b c) ≤ 9 / 25 := by
  have hp := tripleP_lower_unit ha hb hc
  have hab := (dot_ball_bounds ha.le hb.le).2
  have hac := (dot_ball_bounds ha.le hc.le).2
  have hbc := (dot_ball_bounds hb.le hc.le).2
  have hid : (9 + 3 * tripleP a b c)^2 - normSq (tripleV a b c) =
      4 * (((1 - dot b c) - (1 - dot a c))^2 +
        ((1 - dot b c) - (1 - dot a b))^2 +
        ((1 - dot a c) - (1 - dot a b))^2) +
      6 * (1 - dot b c) * (1 - dot a c) * (1 - dot a b) := by
    rw [tripleV_norm, ha, hb, hc]
    unfold tripleP
    ring
  have hprod : 0 ≤ (1 - dot b c) * (1 - dot a c) * (1 - dot a b) :=
    mul_nonneg (mul_nonneg (sub_nonneg.mpr hbc) (sub_nonneg.mpr hac))
      (sub_nonneg.mpr hab)
  have hbound : normSq (tripleV a b c) ≤ (9 + 3 * tripleP a b c)^2 := by
    nlinarith [sq_nonneg ((1 - dot b c) - (1 - dot a c)),
      sq_nonneg ((1 - dot b c) - (1 - dot a b)),
      sq_nonneg ((1 - dot a c) - (1 - dot a b))]
  constructor
  · rw [moment_threeProduct]
    linarith
  · rw [tripleMeanU_formula (by linarith), norm_div]
    apply (div_le_iff₀ (sq_pos_of_pos (by linarith : 0 < 5 * (3 + tripleP a b c)))).mpr
    nlinarith

theorem zero_field_mean_bound {b c : Vec3} (hb : normSq b ≤ 1) (hc : normSq c ≤ 1) :
    1 / 2 ≤ moment (threeProduct 0 b c) ∧ normSq (tripleMeanU 0 b c) ≤ 9 / 25 := by
  have hbc := dot_ball_bounds hb hc
  have hp : tripleP 0 b c = dot b c := by simp [tripleP, dot]
  have hv : tripleV 0 b c = fun i => 5 * (b i + c i) := by
    ext i
    simp [tripleV, dot]
  have hnorm : normSq (b + c) = normSq b + normSq c + 2 * dot b c := by
    simp [normSq, dot, Fin.sum_univ_three]
    ring
  have hm : tripleMeanU 0 b c = fun i => (b i + c i) / (3 + dot b c) := by
    rw [tripleMeanU_formula (by rw [hp]; linarith), hv]
    funext i
    rw [hp]
    field_simp
  constructor
  · rw [moment_threeProduct, hp]
    linarith [hbc.1]
  · rw [hm]
    change normSq (fun i => (b + c) i / (3 + dot b c)) ≤ 9 / 25
    rw [norm_div]
    apply (div_le_iff₀ (sq_pos_of_pos (by linarith : 0 < 3 + dot b c))).mpr
    rw [hnorm]
    nlinarith [sq_nonneg (dot b c - 1)]

/-- This restricted three-factor bound suffices for conditional fields: a field
is an actual spin vector, or zero for an absent factor. -/
theorem three_spin_mean_bound (a b c : SpinLetter) :
    1 / 2 ≤ moment (threeProduct (spinVector a) (spinVector b) (spinVector c)) ∧
      normSq (tripleMeanU (spinVector a) (spinVector b) (spinVector c)) ≤ 9 / 25 := by
  rcases a with _ | a
  · exact zero_field_mean_bound (spinVector_ball b) (spinVector_ball c)
  rcases b with _ | b
  · have he : threeProduct (spinVector (some a)) 0 (spinVector c) =
        threeProduct 0 (spinVector (some a)) (spinVector c) := by
      funext n
      unfold threeProduct
      ring
    have h := zero_field_mean_bound (spinVector_ball (some a)) (spinVector_ball c)
    simp only [spinVector] at he h ⊢
    unfold tripleMeanU at h ⊢
    simpa only [he] using h
  rcases c with _ | c
  · have he : threeProduct (spinVector (some a)) (spinVector (some b)) 0 =
        threeProduct 0 (spinVector (some a)) (spinVector (some b)) := by
      funext n
      unfold threeProduct
      ring
    have h := zero_field_mean_bound (spinVector_ball (some a)) (spinVector_ball (some b))
    simp only [spinVector] at he h ⊢
    unfold tripleMeanU at h ⊢
    simpa only [he] using h
  exact three_unit_mean_bound (icoVector_unit a) (icoVector_unit b) (icoVector_unit c)

def tripleMean (s : Status) (a b c : Vec3) : Vec3 :=
  fun i => siteFunctional s (fun n => n i * threeProduct a b c n) /
    siteFunctional s (threeProduct a b c)

theorem three_spin_local_bound (s : Status) (hs : s = .U ∨ s = .D)
    (a b c : SpinLetter) :
    0 < siteFunctional s (threeProduct (spinVector a) (spinVector b) (spinVector c)) ∧
      normSq (tripleMean s (spinVector a) (spinVector b) (spinVector c)) ≤ 9 / 25 := by
  have hU := three_spin_mean_bound a b c
  let A := moment (threeProduct (spinVector a) (spinVector b) (spinVector c))
  have hA : 1 / 2 ≤ A := hU.1
  have hAp : 0 < A := by linarith
  rcases hs with rfl | rfl
  · constructor
    · rw [site_U_eq_moment]
      exact lt_of_lt_of_le (by norm_num) hU.1
    · have hu := hU.2
      unfold tripleMeanU at hu
      unfold tripleMean
      simpa only [site_U_eq_moment] using hu
  · have hd : siteFunctional .D
        (threeProduct (spinVector a) (spinVector b) (spinVector c)) =
          (3 * A + 2) / 5 := by
      rw [site_D_eq_moment]
      simp only [threeProduct, dot, Pi.zero_apply, zero_mul, Finset.sum_const_zero,
        add_zero, mul_one]
      change 2 / 5 + 3 / 5 * A = _
      ring
    have hden : 0 < 3 * A + 2 := by linarith
    have he : tripleMean .D (spinVector a) (spinVector b) (spinVector c) =
        fun i => (3 * A / (3 * A + 2)) *
          tripleMeanU (spinVector a) (spinVector b) (spinVector c) i := by
      funext i
      unfold tripleMean tripleMeanU
      rw [hd, site_D_eq_moment]
      simp only [Pi.zero_apply, zero_mul, mul_zero, zero_add]
      change (3 / 5 * _) / ((3 * A + 2) / 5) = (3 * A / (3 * A + 2)) * (_ / A)
      field_simp
    have hscale0 : 0 ≤ 3 * A / (3 * A + 2) := by positivity
    have hscale1 : 3 * A / (3 * A + 2) ≤ 1 := by
      apply (div_le_one hden).mpr
      linarith
    have hscaleSq : (3 * A / (3 * A + 2))^2 ≤ 1 := by nlinarith
    constructor
    · rw [hd]
      positivity
    · rw [he]
      have he' : normSq (fun i => (3 * A / (3 * A + 2)) *
          tripleMeanU (spinVector a) (spinVector b) (spinVector c) i) =
          (3 * A / (3 * A + 2))^2 *
            normSq (tripleMeanU (spinVector a) (spinVector b) (spinVector c)) := by
        simp [normSq, dot, Fin.sum_univ_three]
        ring
      rw [he']
      exact (mul_le_mul_of_nonneg_right hscaleSq (normSq_nonnegative _)).trans (by simpa using hU.2)

end AKLT.W.REC019
