import AKLT.W.REC021.FreePositivity

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC021

theorem normSq_nonneg (a : Vec3) : 0 ≤ normSq a := by
  exact Finset.sum_nonneg (s := Finset.univ) (fun i _ => mul_self_nonneg (a i))

theorem dot_cauchy (a b : Vec3) : dot a b ^ 2 ≤ normSq a * normSq b := by
  have he : normSq a * normSq b - dot a b ^ 2 =
      (a 0 * b 1 - a 1 * b 0)^2 + (a 0 * b 2 - a 2 * b 0)^2 +
        (a 1 * b 2 - a 2 * b 1)^2 := by
    simp only [normSq, dot, Fin.sum_univ_three]
    ring
  nlinarith only [he, sq_nonneg (a 0 * b 1 - a 1 * b 0),
    sq_nonneg (a 0 * b 2 - a 2 * b 0), sq_nonneg (a 1 * b 2 - a 2 * b 1)]

theorem dot_ball_le {a b : Vec3} (ha : normSq a ≤ 1) (hb : normSq b ≤ 1) :
    dot a b ≤ 1 := by
  have h := dot_cauchy a b
  have hp := mul_le_mul ha hb (normSq_nonneg b) (by norm_num : (0 : ℝ) ≤ 1)
  nlinarith [sq_nonneg (dot a b - 1)]

def cubicWeight (a b c n : Vec3) : ℝ := (1 + dot n a) * (1 + dot n b) * (1 + dot n c)
def cubicA (s : Status) (a b c : Vec3) : ℝ := siteFunctional s (cubicWeight a b c)
def cubicB (s : Status) (a b c : Vec3) : Vec3 :=
  fun i => siteFunctional s (fun n => n i * cubicWeight a b c n)

theorem normSq_div (v : Vec3) (d : ℝ) :
    normSq (fun i => v i / d) = normSq v / d^2 := by
  simp only [normSq, dot, Fin.sum_univ_three]
  ring

/-- A sum-of-squares proof of the three-field bound. The three additional
terms extend the unit-field identity to the closed unit ball. -/
theorem cubic_U_bound (a b c : Vec3) (ha : normSq a ≤ 1) (hb : normSq b ≤ 1)
    (hc : normSq c ≤ 1) :
    0 < cubicA .U a b c ∧
      normSq (cubicB .U a b c) ≤ (9 / 25 : ℝ) * (cubicA .U a b c)^2 := by
  let p := dot a b + dot a c + dot b c
  let V : Vec3 := fun i => (5 + dot b c) * a i + (5 + dot a c) * b i +
    (5 + dot a b) * c i
  have hab := dot_ball_le ha hb
  have hac := dot_ball_le ha hc
  have hbc := dot_ball_le hb hc
  have hp : -(3 / 2 : ℝ) ≤ p := by
    have hz := normSq_nonneg (a + b + c)
    have he : normSq (a + b + c) = normSq a + normSq b + normSq c + 2 * p := by
      simp [normSq, dot, Fin.sum_univ_three, p]
      ring
    linarith
  have he : 9 * (3 + p)^2 - normSq V =
      4 * ((dot a b - dot a c)^2 + (dot a b - dot b c)^2 + (dot a c - dot b c)^2) +
      6 * (1 - dot a b) * (1 - dot a c) * (1 - dot b c) +
      (1 - normSq a) * (5 + dot b c)^2 +
      (1 - normSq b) * (5 + dot a c)^2 +
      (1 - normSq c) * (5 + dot a b)^2 := by
    simp only [normSq, dot, Fin.sum_univ_three, V, p]
    ring
  have hv : normSq V ≤ 9 * (3 + p)^2 := by
    have hprod : 0 ≤ 6 * (1 - dot a b) * (1 - dot a c) * (1 - dot b c) := by positivity
    have h1 : 0 ≤ (1 - normSq a) * (5 + dot b c)^2 := by positivity
    have h2 : 0 ≤ (1 - normSq b) * (5 + dot a c)^2 := by positivity
    have h3 : 0 ≤ (1 - normSq c) * (5 + dot a b)^2 := by positivity
    nlinarith only [he, hprod, h1, h2, h3, sq_nonneg (dot a b - dot a c),
      sq_nonneg (dot a b - dot b c), sq_nonneg (dot a c - dot b c)]
  have hA : cubicA .U a b c = (3 + p) / 3 := by
    change siteFunctional .U (fun n => (1 + dot n a) * (1 + dot n b) * (1 + dot n c)) = _
    rw [site_cubic_U]
    dsimp [p]
    ring
  have hB : cubicB .U a b c = fun i => V i / 15 := by
    funext i
    change siteFunctional .U (fun n => n i *
      ((1 + dot n a) * (1 + dot n b) * (1 + dot n c))) = _
    rw [site_cubic_first_U]
    dsimp [V]
    ring
  rw [hA, hB, normSq_div]
  constructor
  · linarith
  · nlinarith only [hv]

theorem cubic_bound (s : Status) (hs : s = .U ∨ s = .D)
    (a b c : Vec3) (ha : normSq a ≤ 1) (hb : normSq b ≤ 1) (hc : normSq c ≤ 1) :
    0 < cubicA s a b c ∧
      normSq (cubicB s a b c) ≤ (9 / 25 : ℝ) * (cubicA s a b c)^2 := by
  have hu := cubic_U_bound a b c ha hb hc
  rcases hs with rfl | rfl
  · exact hu
  · have hA : cubicA .D a b c = (3 / 5 : ℝ) * cubicA .U a b c + 2 / 5 := by
      rw [cubicA, site_D_mix]
      simp [cubicWeight, dot, cubicA]
    have hB : cubicB .D a b c = fun i => (3 / 5 : ℝ) * cubicB .U a b c i := by
      funext i
      simp [cubicB, site_D_mix]
    have hn : normSq (cubicB .D a b c) = (9 / 25 : ℝ) * normSq (cubicB .U a b c) := by
      rw [hB]
      simp only [normSq, dot, Fin.sum_univ_three]
      ring
    rw [hA, hn]
    constructor
    · linarith [hu.1]
    · nlinarith [hu.1, hu.2]

theorem cubic_mean_bound (s : Status) (hs : s = .U ∨ s = .D)
    (a b c : Vec3) (ha : normSq a ≤ 1) (hb : normSq b ≤ 1) (hc : normSq c ≤ 1) :
    normSq (fun i => cubicB s a b c i / cubicA s a b c) ≤ (9 / 25 : ℝ) := by
  have h := cubic_bound s hs a b c ha hb hc
  rw [normSq_div]
  exact (div_le_iff₀ (sq_pos_of_pos h.1)).mpr h.2

theorem triple_mean_lower (a b c : Vec3)
    (ha : normSq a ≤ (9 / 25 : ℝ)) (hb : normSq b ≤ (9 / 25 : ℝ))
    (hc : normSq c ≤ (9 / 25 : ℝ)) :
    -(27 / 50 : ℝ) ≤ dot a b + dot a c + dot b c := by
  have h := normSq_nonneg (a + b + c)
  have he : normSq (a + b + c) = normSq a + normSq b + normSq c +
      2 * (dot a b + dot a c + dot b c) := by
    simp only [normSq, dot, Fin.sum_univ_three, Pi.add_apply]
    ring
  linarith

#print axioms cubic_U_bound
#print axioms cubic_bound
#print axioms cubic_mean_bound
#print axioms triple_mean_lower

end AKLT.W.REC021
