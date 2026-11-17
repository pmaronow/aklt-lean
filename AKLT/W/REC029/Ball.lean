module
public import AKLT.W.REC029.Algebra

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC029

theorem site_linear (s : Status) (c d : ℝ) (f g : Vec3 → ℝ) :
    siteFunctional s (fun n => c * f n + d * g n) =
      c * siteFunctional s f + d * siteFunctional s g := by
  unfold siteFunctional
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem good_mix {f g : Vec3 → ℝ} {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1)
    (hf : Good f) (hg : Good g) : Good (fun n => t * f n + (1-t) * g n) := by
  have hA := site_linear .U t (1-t) f g
  have hN : asE (numerator .U (fun n => t * f n + (1-t) * g n)) =
      t • asE (numerator .U f) + (1-t) • asE (numerator .U g) := by
    ext i
    change siteFunctional .U (fun n => n i * (t * f n + (1-t) * g n)) = _
    have he : (fun n : Vec3 => n i * (t * f n + (1-t) * g n)) =
        (fun n => t * (n i * f n) + (1-t) * (n i * g n)) := by
      funext n
      ring
    rw [he, site_linear]
    rfl
  refine ⟨?_, ?_⟩
  · rw [hA]
    nlinarith [mul_nonneg ht (sub_nonneg.mpr hf.1),
      mul_nonneg (sub_nonneg.mpr ht') (sub_nonneg.mpr hg.1)]
  · rw [hN, hA]
    calc
      _ ≤ ‖t • asE (numerator .U f)‖ + ‖(1-t) • asE (numerator .U g)‖ := norm_add_le _ _
      _ = t * ‖asE (numerator .U f)‖ + (1-t) * ‖asE (numerator .U g)‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg ht, abs_of_nonneg (sub_nonneg.mpr ht')]
      _ ≤ t * ((3/5 : ℝ) * siteFunctional .U f) +
          (1-t) * ((3/5 : ℝ) * siteFunctional .U g) := by
        gcongr
        · exact hf.2
        · exact hg.2
      _ = _ := by ring

theorem normSq_div (v : Vec3) (c : ℝ) :
    normSq (fun i => v i / c) = normSq v / c^2 := by
  simp only [normSq, dot, div_mul_div_comm, ← Finset.sum_div, pow_two]

def axis : UnitVector := ⟨![1,0,0], by norm_num [normSq, dot, Fin.sum_univ_three]⟩

def negUnit (e : UnitVector) : UnitVector :=
  ⟨-e.val, by simpa [normSq, dot] using e.property⟩

/-- An arbitrary ball field is a convex combination of antipodal unit fields. -/
theorem ball_split (b : Vec3) (hb : normSq b ≤ 1) :
    ∃ t : ℝ, ∃ e : UnitVector, 0 ≤ t ∧ t ≤ 1 ∧
      ∀ n : Vec3, 1 + dot n b =
        t * (1 + dot n e.val) + (1-t) * (1 + dot n (-e.val)) := by
  let r := ‖asE b‖
  have hr : 0 ≤ r := norm_nonneg _
  have hr1 : r ≤ 1 := by
    rw [normSq_eq] at hb
    dsimp [r]
    nlinarith [norm_nonneg (asE b)]
  by_cases hz : r = 0
  · have hb0 : b = 0 := by
      have h := norm_eq_zero.mp hz
      funext i
      exact congrArg (fun x : E3 => x i) h
    refine ⟨1/2, axis, by norm_num, by norm_num, ?_⟩
    intro n
    rw [hb0]
    simp [dot, Fin.sum_univ_three, axis]
    ring
  · let e : UnitVector := ⟨(fun i => b i / r), by
      rw [normSq_div, normSq_eq]
      change r^2 / r^2 = 1
      exact div_self (pow_ne_zero _ hz)⟩
    refine ⟨(1+r)/2, e, by positivity, by linarith, ?_⟩
    intro n
    dsimp [e, dot]
    simp only [Fin.sum_univ_three]
    field_simp
    ring

/-- Insert one ball field in any fixed product, using the same mixture for
its scalar and vector moments. -/
theorem good_slot (F : Vec3 → ℝ) (b : Vec3) (hb : normSq b ≤ 1)
    (h : ∀ e : UnitVector, Good (fun n => (1 + dot n e.val) * F n)) :
    Good (fun n => (1 + dot n b) * F n) := by
  obtain ⟨t, e, ht, ht', he⟩ := ball_split b hb
  have hmix := good_mix ht ht' (h e) (h (negUnit e))
  have hid : (fun n => (1 + dot n b) * F n) =
      (fun n => t * ((1 + dot n e.val) * F n) +
        (1-t) * ((1 + dot n (negUnit e).val) * F n)) := by
    funext n
    rw [he]
    dsimp only [negUnit]
    ring
  rw [hid]
  exact hmix

theorem ball_triple_good (a : Fin 3 → Vec3) (ha : ∀ j, normSq (a j) ≤ 1) :
    Good (localProduct a) := by
  have h0 : Good (fun n => (1 + dot n (a 0)) *
      ((1 + dot n (a 1)) * (1 + dot n (a 2)))) := by
    apply good_slot _ (a 0) (ha 0)
    intro e0
    have h1 : Good (fun n => (1 + dot n (a 1)) *
        ((1 + dot n e0.val) * (1 + dot n (a 2)))) := by
      apply good_slot _ (a 1) (ha 1)
      intro e1
      have h2 : Good (fun n => (1 + dot n (a 2)) *
          ((1 + dot n e0.val) * (1 + dot n e1.val))) := by
        apply good_slot _ (a 2) (ha 2)
        intro e2
        have hu := unit_good ![e0.val, e1.val, e2.val] (by
          intro j
          fin_cases j
          · exact e0.property
          · exact e1.property
          · exact e2.property)
        convert hu using 1
        funext n
        simp only [localProduct, Fin.prod_univ_three, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val]
        ring
      convert h2 using 1
      funext n
      ring
    convert h1 using 1
    funext n
    ring
  convert h0 using 1
  funext n
  simp [localProduct, Fin.prod_univ_three, mul_assoc]

/-- Pad missing slots by zero fields before the three-slot convex argument. -/
theorem ball_good {k : ℕ} (hk : k ≤ 3) (b : Fin k → Vec3)
    (hb : ∀ j, normSq (b j) ≤ 1) : Good (localProduct b) := by
  interval_cases k
  · have h := ball_triple_good (fun _ => 0) (by
      intro j
      norm_num [normSq, dot])
    convert h using 1
    funext n
    simp [localProduct, dot]
  · have h := ball_triple_good ![b 0, 0, 0] (by
      intro j
      fin_cases j
      · exact hb 0
      all_goals norm_num [normSq, dot])
    convert h using 1
    funext n
    simp [localProduct, Fin.prod_univ_three, dot]
  · have h := ball_triple_good ![b 0, b 1, 0] (by
      intro j
      fin_cases j
      · exact hb 0
      · exact hb 1
      · norm_num [normSq, dot])
    convert h using 1
    funext n
    simp [localProduct, Fin.prod_univ_three, Fin.prod_univ_two, dot]
  · exact ball_triple_good b hb

theorem U_ball_bound {k : ℕ} (hk : k ≤ 3) (b : Fin k → Vec3)
    (hb : ∀ j, normSq (b j) ≤ 1) :
    0 < siteFunctional .U (localProduct b) ∧
      normSq (localMean .U b) ≤ (3/5 : ℝ)^2 := by
  have h := ball_good hk b hb
  have hA : 0 < siteFunctional .U (localProduct b) := by linarith [h.1]
  refine ⟨hA, ?_⟩
  have hs : normSq (numerator .U (localProduct b)) ≤
      ((3/5 : ℝ) * siteFunctional .U (localProduct b))^2 := by
    rw [normSq_eq]
    nlinarith [h.2, norm_nonneg (asE (numerator .U (localProduct b)))]
  change normSq (fun i => numerator .U (localProduct b) i /
    siteFunctional .U (localProduct b)) ≤ _
  rw [normSq_div]
  apply (div_le_iff₀ (sq_pos_of_pos hA)).2
  nlinarith [hs]

theorem site_D (f : Vec3 → ℝ) :
    siteFunctional .D f = (3/5 : ℝ) * siteFunctional .U f + (2/5 : ℝ) * f 0 := by
  simp [siteFunctional, Fintype.sum_option, spinWeight, spinVector,
    ← Finset.mul_sum]
  ring

/-- The zero atom increases the denominator and contributes no numerator. -/
theorem D_ball_bound {k : ℕ} (hk : k ≤ 3) (b : Fin k → Vec3)
    (hb : ∀ j, normSq (b j) ≤ 1) :
    0 < siteFunctional .D (localProduct b) ∧
      normSq (localMean .D b) ≤ (3/5 : ℝ)^2 := by
  have h := ball_good hk b hb
  have hA : 0 < siteFunctional .U (localProduct b) := by linarith [h.1]
  have hD : siteFunctional .D (localProduct b) =
      (3/5 : ℝ) * siteFunctional .U (localProduct b) + 2/5 := by
    rw [site_D]
    simp [localProduct, dot]
  have hN : numerator .D (localProduct b) =
      fun i => (3/5 : ℝ) * numerator .U (localProduct b) i := by
    funext i
    simp [numerator, site_D]
  have hDpos : 0 < siteFunctional .D (localProduct b) := by rw [hD]; positivity
  refine ⟨hDpos, ?_⟩
  have hs : normSq (numerator .U (localProduct b)) ≤
      ((3/5 : ℝ) * siteFunctional .U (localProduct b))^2 := by
    rw [normSq_eq]
    nlinarith [h.2, norm_nonneg (asE (numerator .U (localProduct b)))]
  change normSq (fun i => numerator .D (localProduct b) i /
    siteFunctional .D (localProduct b)) ≤ _
  rw [normSq_div, hN, normSq_scale]
  apply (div_le_iff₀ (sq_pos_of_pos hDpos)).2
  rw [hD]
  nlinarith [hs]

theorem tip_mean_bound {k : ℕ} (hk : k ≤ 3) (b : Fin k → Vec3)
    (hb : ∀ j, normSq (b j) ≤ 1) (s : Status) (hs : s = .U ∨ s = .D) :
    0 < siteFunctional s (localProduct b) ∧
      normSq (localMean s b) ≤ (3/5 : ℝ)^2 := by
  rcases hs with rfl | rfl
  · exact U_ball_bound hk b hb
  · exact D_ball_bound hk b hb

end AKLT.W.REC029
