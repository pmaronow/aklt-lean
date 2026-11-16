import AKLT.W.REC037.Moments
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

theorem sum_pairing_ikjl (a b c d : Fin 3 → ℝ) :
    (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
      a i * b j * c k * d l * (if i = k ∧ j = l then 1 else 0)) =
      (∑ i, a i * c i) * (∑ j, b j * d j) := by
  calc
    _ = ∑ i, ∑ k, ∑ j, ∑ l,
        a i * c k * b j * d l * (if i = k ∧ j = l then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro j hj
      ring_nf
    _ = (∑ i, a i * c i) * (∑ j, b j * d j) := sum_diag_pair a c b d

theorem sum_pairing_iljk (a b c d : Fin 3 → ℝ) :
    (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
      a i * b j * c k * d l * (if i = l ∧ j = k then 1 else 0)) =
      (∑ i, a i * d i) * (∑ j, b j * c j) := by
  calc
    _ = ∑ i, ∑ j, ∑ l, ∑ k,
        a i * b j * c k * d l * (if i = l ∧ j = k then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact Finset.sum_comm
    _ = ∑ i, ∑ l, ∑ j, ∑ k,
        a i * b j * c k * d l * (if i = l ∧ j = k then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_comm
    _ = ∑ i, ∑ l, ∑ j, ∑ k,
        a i * d l * b j * c k * (if i = l ∧ j = k then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro l hl
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = (∑ i, a i * d i) * (∑ j, b j * c j) := sum_diag_pair a d b c

theorem moment_add (f g : Vec3 → ℝ) :
    moment (fun v => f v + g v) = moment f + moment g := by
  unfold moment
  rw [Finset.sum_add_distrib]
  ring

theorem dot_comm (a b : Vec3) : dot a b = dot b a := by
  unfold dot
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem moment_dot_one (a : Vec3) : moment (fun n => dot a n) = 0 := by
  rw [show (fun n => dot a n) = (fun n => ∑ i, a i * n i) by funext n; simp [dot]]
  rw [moment_sum]
  simp_rw [moment_smul, moment_first_coord]
  simp

theorem dot_two_expand (a b n : Vec3) :
    dot a n * dot b n =
      ∑ i, ∑ j, (a i * b j) * (n i * n j) := by
  simp only [dot]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem moment_dot_two (a b : Vec3) :
    moment (fun n => dot a n * dot b n) = dot a b / 3 := by
  have hexpand : (fun n => dot a n * dot b n) =
      (fun n => ∑ i, ∑ j, (a i * b j) * (n i * n j)) := by
    funext n
    exact dot_two_expand a b n
  rw [hexpand, moment_sum]
  simp_rw [moment_sum, moment_smul, moment_second_tensor]
  have hcontract :
      (∑ i, ∑ j, a i * b j * (if i = j then (1 / 3 : ℝ) else 0)) =
        (1 / 3 : ℝ) * ∑ i, a i * b i := by
    calc
      _ = ∑ i, ∑ j, (1 / 3 : ℝ) *
          (a i * b j * (if i = j then 1 else 0)) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        split_ifs <;> ring
      _ = (1 / 3 : ℝ) *
          (∑ i, ∑ j, a i * b j * (if i = j then 1 else 0)) := by
        simp_rw [← Finset.mul_sum]
      _ = (1 / 3 : ℝ) * ∑ i, a i * b i := by rw [sum_diag2]
  rw [hcontract]
  simp [dot]
  ring


theorem moment_dot_three (a b c : Vec3) :
    moment (fun n => dot a n * dot b n * dot c n) = 0 := by
  have hexpand : (fun n => dot a n * dot b n * dot c n) =
      (fun n => ∑ i, ∑ j, ∑ k,
        ((a i * b j) * c k) * (n i * n j * n k)) := by
    funext n
    rw [dot_two_expand a b n]
    simp only [dot]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hexpand, moment_sum]
  simp_rw [moment_sum, moment_smul, moment_third_tensor]
  simp


theorem moment_dot_four (a b c d : Vec3) :
    moment (fun n => dot a n * dot b n * dot c n * dot d n) =
      (dot a b * dot c d + dot a c * dot b d + dot a d * dot b c) / 15 := by
  have hexpand : (fun n => dot a n * dot b n * dot c n * dot d n) =
      (fun n => ∑ i, ∑ j, ∑ k, ∑ l,
        (((a i * b j) * c k) * d l) * (n i * n j * n k * n l)) := by
    funext n
    rw [show dot a n * dot b n * dot c n * dot d n =
      (dot a n * dot b n) * (dot c n * dot d n) by ring]
    rw [dot_two_expand a b n, dot_two_expand c d n]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l hl
    ring
  rw [hexpand, moment_sum]
  simp_rw [moment_sum, moment_smul, moment_four_tensor]
  have hsplit :
      (∑ i, ∑ j, ∑ k, ∑ l,
        (((a i * b j) * c k) * d l) *
          (((if i = j ∧ k = l then 1 else 0) +
              (if i = k ∧ j = l then 1 else 0) +
              (if i = l ∧ j = k then 1 else 0)) / 15)) =
        (1 / 15 : ℝ) *
          ((∑ i, ∑ j, ∑ k, ∑ l,
              (((a i * b j) * c k) * d l) * (if i = j ∧ k = l then 1 else 0)) +
            (∑ i, ∑ j, ∑ k, ∑ l,
              (((a i * b j) * c k) * d l) * (if i = k ∧ j = l then 1 else 0)) +
            (∑ i, ∑ j, ∑ k, ∑ l,
              (((a i * b j) * c k) * d l) * (if i = l ∧ j = k then 1 else 0))) := by
    have hpoint (i j k l : Fin 3) :
        (((a i * b j) * c k) * d l) *
          (((if i = j ∧ k = l then 1 else 0) +
              (if i = k ∧ j = l then 1 else 0) +
              (if i = l ∧ j = k then 1 else 0)) / 15) =
        (1 / 15 : ℝ) * ((((a i * b j) * c k) * d l) *
            (if i = j ∧ k = l then 1 else 0)) +
          (1 / 15 : ℝ) * ((((a i * b j) * c k) * d l) *
            (if i = k ∧ j = l then 1 else 0)) +
          (1 / 15 : ℝ) * ((((a i * b j) * c k) * d l) *
            (if i = l ∧ j = k then 1 else 0)) := by
      ring
    simp_rw [hpoint]
    simp_rw [Finset.sum_add_distrib]
    simp_rw [← Finset.mul_sum]
    ring
  rw [hsplit, sum_diag_pair, sum_pairing_ikjl, sum_pairing_iljk]
  simp [dot]
  ring


theorem moment_mixed_two (a b : Vec3) :
    moment (fun n => dot a n * dot n b) = dot a b / 3 := by
  apply (congrArg moment ?_).trans (moment_dot_two a b)
  funext n
  rw [dot_comm n b]

theorem moment_mixed_three (a b c : Vec3) :
    moment (fun n => dot a n * dot n b * dot n c) = 0 := by
  apply (congrArg moment ?_).trans (moment_dot_three a b c)
  funext n
  rw [dot_comm n b, dot_comm n c]

theorem moment_mixed_four (a b c d : Vec3) :
    moment (fun n => dot a n * dot n b * dot n c * dot n d) =
      (dot a b * dot c d + dot a c * dot b d + dot a d * dot b c) / 15 := by
  apply (congrArg moment ?_).trans (moment_dot_four a b c d)
  funext n
  rw [dot_comm n b, dot_comm n c, dot_comm n d]

theorem siteU_three_factors (a b c d : Vec3) :
    siteFunctional .U (fun n => dot a n * (1 + dot n b) *
      (1 + dot n c) * (1 + dot n d)) =
      (dot a b + dot a c + dot a d) / 3 +
        (dot a b * dot c d + dot a c * dot b d + dot a d * dot b c) / 15 := by
  rw [siteU_eq_moment]
  have hpoly : (fun n : Vec3 => dot a n * (1 + dot n b) *
        (1 + dot n c) * (1 + dot n d)) =
      (fun n => dot a n + dot a n * dot n b + dot a n * dot n c +
        dot a n * dot n d + dot a n * dot n b * dot n c +
        dot a n * dot n b * dot n d + dot a n * dot n c * dot n d +
        dot a n * dot n b * dot n c * dot n d) := by
    funext n
    ring
  rw [hpoly]
  simp_rw [moment_add, moment_dot_one a, moment_mixed_two, moment_mixed_three,
    moment_mixed_four]
  ring

theorem siteU_dot (a : Vec3) :
    siteFunctional .U (fun n => dot a n) = 0 := by
  rw [siteU_eq_moment]
  exact moment_dot_one a

theorem siteU_dot_two (a b : Vec3) :
    siteFunctional .U (fun n => dot n a * dot n b) = dot a b / 3 := by
  rw [siteU_eq_moment]
  apply (congrArg moment ?_).trans (moment_dot_two a b)
  funext n
  rw [dot_comm n a, dot_comm n b]

theorem siteU_dot_three (a b c : Vec3) :
    siteFunctional .U (fun n => dot n a * dot n b * dot n c) = 0 := by
  rw [siteU_eq_moment]
  apply (congrArg moment ?_).trans (moment_dot_three a b c)
  funext n
  rw [dot_comm n a, dot_comm n b, dot_comm n c]

theorem siteU_dot_four (a b c d : Vec3) :
    siteFunctional .U (fun n => dot n a * dot n b * dot n c * dot n d) =
      (dot a b * dot c d + dot a c * dot b d + dot a d * dot b c) / 15 := by
  rw [siteU_eq_moment]
  apply (congrArg moment ?_).trans (moment_dot_four a b c d)
  funext n
  rw [dot_comm n a, dot_comm n b, dot_comm n c, dot_comm n d]


theorem moment_left_dot (a : Vec3) : moment (fun n => dot n a) = 0 := by
  apply (congrArg moment ?_).trans (moment_dot_one a)
  funext n
  exact (dot_comm n a).trans rfl

theorem moment_left_dot_two (a b : Vec3) :
    moment (fun n => dot n a * dot n b) = dot a b / 3 := by
  apply (congrArg moment ?_).trans (moment_dot_two a b)
  funext n
  rw [dot_comm n a, dot_comm n b]

theorem siteU_one_factor (a b : Vec3) :
    siteFunctional .U (fun n => dot a n * (1 + dot n b)) = dot a b / 3 := by
  simpa [dot] using siteU_three_factors a b 0 0

theorem siteU_two_factors (a b c : Vec3) :
    siteFunctional .U (fun n => dot a n * (1 + dot n b) * (1 + dot n c)) =
      (dot a b + dot a c) / 3 := by
  simpa [dot] using siteU_three_factors a b c 0

theorem siteU_zero_factors (a : Vec3) :
    siteFunctional .U (fun n => dot a n) = 0 := siteU_dot a

theorem siteD_dot (a : Vec3) :
    siteFunctional .D (fun n => dot n a) = 0 := by
  rw [siteD_eq_moment]
  rw [moment_left_dot]
  simp [dot]

theorem siteD_product_two (a b : Vec3) :
    siteFunctional .D (fun n => (1 + dot n a) * (1 + dot n b)) =
      1 + dot a b / 5 := by
  rw [siteD_eq_moment]
  have hpoly : (fun n : Vec3 => (1 + dot n a) * (1 + dot n b)) =
      (fun n => 1 + dot n a + dot n b + dot n a * dot n b) := by
    funext n
    ring
  rw [hpoly]
  rw [moment_add, moment_add, moment_add]
  rw [moment_left_dot, moment_left_dot, moment_left_dot_two]
  have hconst : moment (fun _ : Vec3 => (1 : ℝ)) = 1 := by
    exact moment_const
  rw [hconst]
  simp [dot]
  ring

theorem siteD_one_factor (a : Vec3) :
    siteFunctional .D (fun n => 1 + dot n a) = 1 := by
  simpa [dot] using siteD_product_two a (0 : Vec3)

theorem siteD_const : siteFunctional .D (fun _ : Vec3 => (1 : ℝ)) = 1 := by
  simpa [dot] using siteD_product_two (0 : Vec3) (0 : Vec3)


theorem uStepMoment : AKLT.Blueprint.Rec.UStepMomentStatement := by
  intro k hk a u
  have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hk' with h | h | h | h <;> subst k
  · simpa [Fin.prod_univ_zero] using siteU_zero_factors a
  · have hL : siteFunctional .U (fun n => dot a n *
        (∏ i : Fin 1, (1 + dot n (u i)))) = dot a (u 0) / 3 := by
      convert siteU_one_factor a (u 0) using 1
      · congr 1
        funext n
        simp [Fin.prod_univ_succ, Fin.prod_univ_zero]
    have he0 : (Finset.univ.erase (0 : Fin 1)) = ∅ := by
      ext j
      fin_cases j <;> simp
    rw [hL]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
    rw [he0]
    simp [Fin.sum_univ_succ, Fin.sum_univ_zero, siteD_const]
    ring
  · have hL : siteFunctional .U (fun n => dot a n *
        (∏ i : Fin 2, (1 + dot n (u i)))) =
        (dot a (u 0) + dot a (u 1)) / 3 := by
      convert siteU_two_factors a (u 0) (u 1) using 1
      · congr 1
        funext n
        simp [Fin.prod_univ_succ, Fin.prod_univ_zero]
        ring
    have he0 : (Finset.univ.erase (0 : Fin 2)) = {1} := by
      ext j
      fin_cases j <;> simp
    have he1 : (Finset.univ.erase (Fin.succ (0 : Fin 1))) = {0} := by
      ext j
      fin_cases j <;> simp
    rw [hL]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
    rw [he0, he1]
    simp [Fin.sum_univ_succ, siteD_one_factor]
    ring
  · have hL : siteFunctional .U (fun n => dot a n *
        (∏ i : Fin 3, (1 + dot n (u i)))) =
        (dot a (u 0) + dot a (u 1) + dot a (u 2)) / 3 +
          (dot a (u 0) * dot (u 1) (u 2) +
            dot a (u 1) * dot (u 0) (u 2) +
            dot a (u 2) * dot (u 0) (u 1)) / 15 := by
      convert siteU_three_factors a (u 0) (u 1) (u 2) using 1
      · congr 1
        funext n
        simp [Fin.prod_univ_succ, Fin.prod_univ_zero]
        ring
    have he0 : (Finset.univ.erase (0 : Fin 3)) = {1, 2} := by
      ext j
      fin_cases j <;> simp
    have he1 : (Finset.univ.erase (Fin.succ (0 : Fin 2))) = {0, 2} := by
      ext j
      fin_cases j <;> simp
    have he2 : (Finset.univ.erase (Fin.succ (Fin.succ (0 : Fin 1)))) = {0, 1} := by
      ext j
      fin_cases j <;> simp
    rw [hL]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
    rw [he0, he1, he2]
    simp [Fin.sum_univ_succ, siteD_product_two]
    ring


end AKLT.W.REC037
