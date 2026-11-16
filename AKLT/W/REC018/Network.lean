import AKLT.W.REC018.Geometry

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC018

variable {G : Finset Plane}

/-- The actual density, with the observable factored out. -/
def netWeight (D : Network G) (τ : PinAssignment G) (b : Bool)
    (n : (x : D.active) → SpinLetter) : ℝ :=
  (∏ x : D.active, spinWeight (D.status x.val) (n x)) *
    (∏ e ∈ D.bonds, (1 + dot (D.spins n e.1) (D.spins n e.2))) *
    ∏ e : originalLegs G,
      if b = true ∧ e.val.1 ∈ D.active then
        1 + dot (τ e).val (D.spins n e.val.1) else 1

theorem partition_sum (D : Network G) (τ : PinAssignment G) (b : Bool)
    (F : (Plane → Vec3) → ℝ) :
    D.partition τ b F = ∑ n, netWeight D τ b n * F (D.spins n) := by
  unfold Network.partition netWeight
  apply Finset.sum_congr rfl
  intro n _
  ring

theorem spins_ball (D : Network G) (n : (x : D.active) → SpinLetter) (x : Plane) :
    normSq (D.spins n x) ≤ 1 := by
  unfold Network.spins
  split
  · exact spin_ball _
  · norm_num [normSq, dot]

theorem spinWeight_nonneg (s : Status) (j : SpinLetter) : 0 ≤ spinWeight s j := by
  cases s <;> cases j <;> norm_num [spinWeight]

theorem netWeight_nonneg (D : Network G) (τ : PinAssignment G) (b : Bool)
    (n : (x : D.active) → SpinLetter) : 0 ≤ netWeight D τ b n := by
  apply mul_nonneg
  · apply mul_nonneg
    · exact Finset.prod_nonneg fun _ _ => spinWeight_nonneg _ _
    · apply Finset.prod_nonneg
      intro e _
      have h := (ball_dot _ _ (spins_ball D n e.1) (spins_ball D n e.2)).1
      linarith
  · apply Finset.prod_nonneg
    intro e _
    split
    · have h := (ball_dot _ _ (τ e).property.le (spins_ball D n e.val.1)).1
      linarith
    · norm_num

theorem partition_one_nonneg (D : Network G) (τ : PinAssignment G) (b : Bool) :
    0 ≤ D.partition τ b (fun _ => 1) := by
  rw [partition_sum]
  exact Finset.sum_nonneg fun _ _ => mul_nonneg (netWeight_nonneg _ _ _ _) zero_le_one

/-- Bounds pass through the normalized finite sum, including a zero normalizer. -/
theorem expectation_bounds (D : Network G) (τ : PinAssignment G) (b : Bool)
    (F : (Plane → Vec3) → ℝ) (l u : ℝ) (hl : l ≤ 0) (hu : 0 ≤ u)
    (hF : ∀ n : (x : D.active) → SpinLetter, l ≤ F (D.spins n) ∧ F (D.spins n) ≤ u) :
    l ≤ D.expectation τ b F ∧ D.expectation τ b F ≤ u := by
  have hz := partition_one_nonneg D τ b
  by_cases hzero : D.partition τ b (fun _ => 1) = 0
  · simpa [Network.expectation, hzero] using And.intro hl hu
  · have hpos : 0 < D.partition τ b (fun _ => 1) := lt_of_le_of_ne hz (Ne.symm hzero)
    have hlo : l * D.partition τ b (fun _ => 1) ≤ D.partition τ b F := by
      simp only [partition_sum, mul_one, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro n _
      nlinarith [mul_le_mul_of_nonneg_left (hF n).1 (netWeight_nonneg D τ b n)]
    have hup : D.partition τ b F ≤ u * D.partition τ b (fun _ => 1) := by
      simp only [partition_sum, mul_one, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro n _
      nlinarith [mul_le_mul_of_nonneg_left (hF n).2 (netWeight_nonneg D τ b n)]
    exact ⟨(le_div_iff₀ hpos).2 hlo, (div_le_iff₀ hpos).2 hup⟩

theorem expectation_add (D : Network G) (τ : PinAssignment G) (b : Bool)
    (F H : (Plane → Vec3) → ℝ) :
    D.expectation τ b (fun n => F n + H n) = D.expectation τ b F + D.expectation τ b H := by
  simp only [Network.expectation, partition_sum, mul_add, Finset.sum_add_distrib, add_div]

theorem pair_bounds (D : Network G) (τ : PinAssignment G) (b : Bool) (f o : Plane) :
    -1 ≤ D.expectation τ b (fun n => dot (n f) (n o)) ∧
    D.expectation τ b (fun n => dot (n f) (n o)) ≤ 1 := by
  apply expectation_bounds D τ b _ (-1) 1 (by norm_num) (by norm_num)
  intro n
  exact ball_dot _ _ (spins_ball D n f) (spins_ball D n o)

theorem triple_mean_lower (D : Network G) (τ : PinAssignment G) (b : Bool) (f g o : Plane) :
    -(3 / 2 : ℝ) ≤ D.expectation τ b (fun n => dot (n f) (n g)) +
      D.expectation τ b (fun n => dot (n f) (n o)) +
      D.expectation τ b (fun n => dot (n g) (n o)) := by
  have h := expectation_bounds D τ b
    (fun n => dot (n f) (n g) + dot (n f) (n o) + dot (n g) (n o))
    (-(3 / 2)) 3 (by norm_num) (by norm_num) (by
      intro n
      refine ⟨triple_dot_lower _ _ _ (spins_ball D n f) (spins_ball D n g)
        (spins_ball D n o), ?_⟩
      have h1 := (ball_dot _ _ (spins_ball D n f) (spins_ball D n g)).2
      have h2 := (ball_dot _ _ (spins_ball D n f) (spins_ball D n o)).2
      have h3 := (ball_dot _ _ (spins_ball D n g) (spins_ball D n o)).2
      linarith)
  simpa only [expectation_add] using h.1

/-- Two non-antipodal atoms suffice for a positive free configuration. -/
def freeConfig (D : Network G) (o : Plane) (x : D.active) : SpinLetter :=
  some (if x.val = o then otherLetter else baseLetter)

theorem two_letter_bond (a b : IcoLetter)
    (ha : a = baseLetter ∨ a = otherLetter) (hb : b = baseLetter ∨ b = otherLetter) :
    0 < 1 + dot (icoVector a) (icoVector b) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · change 0 < 1 + normSq (icoVector baseLetter)
    rw [ico_unit]; norm_num
  · exact base_other_dot.1
  · rw [dot_symm]; exact base_other_dot.1
  · change 0 < 1 + normSq (icoVector otherLetter)
    rw [ico_unit]; norm_num

theorem freeConfig_weight_pos (D : Network G) (τ : PinAssignment G) (o : Plane) :
    0 < netWeight D τ false (freeConfig D o) := by
  classical
  unfold netWeight
  simp only [Bool.false_eq_true, false_and, ite_false, Finset.prod_const_one, mul_one]
  apply mul_pos
  · apply Finset.prod_pos
    intro x _
    have hx : D.status x.val ≠ .X := (Finset.mem_filter.mp x.property).2
    cases hs : D.status x.val <;> simp_all [freeConfig, spinWeight]
  · apply Finset.prod_pos
    intro e he
    have hp := (Finset.mem_filter.mp he).2
    have h1 : e.1 ∈ D.active := hp.1
    have h2 : e.2 ∈ D.active := hp.2.1
    simp only [Network.spins, h1, h2, dite_true, freeConfig, spinVector]
    apply two_letter_bond
    · split_ifs <;> simp
    · split_ifs <;> simp

theorem free_partition_pos (D : Network G) (τ : PinAssignment G) :
    0 < D.partition τ false (fun _ => 1) := by
  classical
  rw [partition_sum]
  simp only [mul_one]
  exact Finset.sum_pos' (fun _ _ => netWeight_nonneg _ _ _ _)
    ⟨freeConfig D (0, 0), Finset.mem_univ _, freeConfig_weight_pos D τ (0, 0)⟩

/-- A free pair at distinct sites cannot be almost surely identical. -/
theorem free_pair_lt_one (D : Network G) (τ : PinAssignment G) (f o : Plane) (hfo : f ≠ o) :
    D.expectation τ false (fun n => dot (n f) (n o)) < 1 := by
  classical
  have hw := freeConfig_weight_pos D τ o
  have hgap : dot (D.spins (freeConfig D o) f) (D.spins (freeConfig D o) o) < 1 := by
    by_cases hf : f ∈ D.active
    · by_cases ho : o ∈ D.active
      · simpa [Network.spins, hf, ho, freeConfig, hfo, spinVector] using base_other_dot.2
      · simp [Network.spins, ho, dot]
    · simp [Network.spins, hf, dot]
  have hstrict : D.partition τ false (fun n => dot (n f) (n o)) <
      D.partition τ false (fun _ => 1) := by
    simp only [partition_sum, mul_one]
    apply Finset.sum_lt_sum
    · intro n _
      exact mul_le_of_le_one_right (netWeight_nonneg D τ false n)
        (ball_dot _ _ (spins_ball D n f) (spins_ball D n o)).2
    · refine ⟨freeConfig D o, Finset.mem_univ _, ?_⟩
      exact mul_lt_of_lt_one_right hw hgap
  exact (div_lt_one (free_partition_pos D τ)).2 hstrict

theorem responseI_pos (D : Network G) (τ : PinAssignment G) (b : Bool) (y o f g : Plane) :
    0 < responseI D τ b y o f g := by
  have h := triple_mean_lower (removeSite D y) τ b f g o
  dsimp [responseI, removedPairMean]
  linarith

theorem responseJ_pos (D : Network G) (τ : PinAssignment G) (b : Bool) (y f g : Plane) :
    0 < responseJ D τ b y f g := by
  have h := (pair_bounds (removeSite D y) τ b f g).1
  dsimp [responseJ, removedPairMean]
  linarith

theorem response_compare (D : Network G) (τ : PinAssignment G) (b : Bool) (y o f g : Plane) :
    3 * responseI D τ b y o f g ≤ 5 * responseJ D τ b y f g := by
  have hf := (pair_bounds (removeSite D y) τ b f o).2
  have hg := (pair_bounds (removeSite D y) τ b g o).2
  dsimp [responseI, responseJ, removedPairMean]
  linarith

theorem free_response_compare (D : Network G) (τ : PinAssignment G)
    (y o f g : Plane) (hfo : f ≠ o) :
    3 * responseI D τ false y o f g < 5 * responseJ D τ false y f g := by
  have hf := free_pair_lt_one (removeSite D y) τ f o hfo
  have hg := (pair_bounds (removeSite D y) τ false g o).2
  dsimp [responseI, responseJ, removedPairMean]
  linarith

end AKLT.W.REC018
