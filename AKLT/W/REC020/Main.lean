import AKLT.Blueprint.Rec.NodesResponse

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC020

private lemma dot_add_right (a b c : Vec3) :
    dot a (b + c) = dot a b + dot a c := by
  unfold dot
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp [Pi.add_apply, mul_add]

private lemma dot_add_left (a b c : Vec3) :
    dot (a + b) c = dot a c + dot b c := by
  unfold dot
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp [Pi.add_apply, add_mul]

private lemma dot_comm (a b : Vec3) : dot a b = dot b a := by
  unfold dot
  apply Finset.sum_congr rfl
  intro i hi
  ring

private lemma normSq_nonneg (a : Vec3) : 0 ≤ normSq a := by
  unfold normSq dot
  apply Finset.sum_nonneg
  intro i hi
  exact mul_self_nonneg (a i)

private lemma sum_fin3 (f : Fin 3 → ℝ) :
    (∑ i : Fin 3, f i) = f 0 + f 1 + f 2 := by
  rw [Fin.sum_univ_succ]
  rw [Fin.sum_univ_succ]
  simp
  ring

private lemma normSq_div (v : Vec3) (c : ℝ) :
    normSq (fun i => v i / c) = normSq v / c ^ 2 := by
  by_cases hc : c = 0
  · simp [hc, normSq, dot]
  · unfold normSq dot
    rw [sum_fin3, sum_fin3]
    simp only [Pi.div_apply]
    field_simp [hc]

private lemma normSq_add (a b : Vec3) :
    normSq (a + b) = normSq a + 2 * dot a b + normSq b := by
  unfold normSq
  rw [dot_add_left, dot_add_right, dot_add_right, dot_comm b a]
  ring

private lemma normSq_add_three (a b c : Vec3) :
    normSq (a + b + c) = normSq a + normSq b + normSq c +
      2 * (dot a b + dot a c + dot b c) := by
  rw [normSq_add (a + b) c, normSq_add a b, dot_add_left]
  ring

private lemma icoVector_normSq (j : IcoLetter) : normSq (icoVector j) = 1 := by
  rcases j with ⟨a, b, c⟩
  have hphi : goldenRatio ^ 2 = goldenRatio + 1 := by
    dsimp [goldenRatio]
    have hs : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    nlinarith
  have hpos : 0 < goldenRatio := by dsimp [goldenRatio]; positivity
  have hr : icoRadius ^ 2 = goldenRatio + 2 := by
    dsimp [icoRadius]
    rw [Real.sq_sqrt (by linarith : 0 ≤ goldenRatio + 2)]
  simp only [icoVector]
  rw [normSq_div]
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp [normSq, dot, signValue, sum_fin3] <;>
      rw [hr] <;>
      field_simp [ne_of_gt (by linarith : 0 < goldenRatio + 2)] <;>
      nlinarith [hphi]

private lemma spinVector_normSq_le_one (j : SpinLetter) :
    normSq (spinVector j) ≤ 1 := by
  cases j with
  | none => simp [spinVector, normSq, dot]
  | some j => simpa [spinVector] using (icoVector_normSq j).le

private lemma dot_lower_of_ball (a b : Vec3)
    (ha : normSq a ≤ 1) (hb : normSq b ≤ 1) : -1 ≤ dot a b := by
  have h := normSq_nonneg (a + b)
  rw [normSq_add] at h
  nlinarith

private lemma factor_nonneg_of_ball (a b : Vec3)
    (ha : normSq a ≤ 1) (hb : normSq b ≤ 1) : 0 ≤ 1 + dot a b := by
  linarith [dot_lower_of_ball a b ha hb]

private lemma spinWeight_nonneg_active (s : Status) (hs : s ≠ .X)
    (j : SpinLetter) : 0 ≤ spinWeight s j := by
  cases s with
  | U => cases j <;> norm_num [spinWeight]
  | D => cases j <;> norm_num [spinWeight]
  | X => contradiction

private def networkTermWeight {G : Finset Plane} (D : Network G)
    (τ : PinAssignment G) (pinned : Bool) (n : (x : D.active) → SpinLetter) : ℝ :=
  (∏ x : D.active, spinWeight (D.status x.val) (n x)) *
    (∏ e ∈ D.bonds, (1 + dot (D.spins n e.1) (D.spins n e.2))) *
    (∏ e : originalLegs G,
      if pinned = true ∧ e.val.1 ∈ D.active then
        1 + dot (τ e).val (D.spins n e.val.1) else 1)

private lemma network_partition_as_sum {G : Finset Plane} (D : Network G)
    (τ : PinAssignment G) (pinned : Bool) (f : (Plane → Vec3) → ℝ) :
    D.partition τ pinned f =
      ∑ n : (x : D.active) → SpinLetter, networkTermWeight D τ pinned n * f (D.spins n) := by
  unfold Network.partition networkTermWeight
  apply Finset.sum_congr rfl
  intro n hn
  ring_nf

private lemma network_weight_nonneg {G : Finset Plane} (D : Network G)
    (τ : PinAssignment G) (pinned : Bool) (n : (x : D.active) → SpinLetter) :
    0 ≤ networkTermWeight D τ pinned n := by
  apply mul_nonneg
  · apply mul_nonneg
    · apply Finset.prod_nonneg
      intro x hx
      exact spinWeight_nonneg_active (D.status x.val) (by
        have hx' : x.val ∈ D.active := x.property
        exact (Finset.mem_filter.mp hx').2) (n x)
    · apply Finset.prod_nonneg
      intro e he
      have hP : D.Present e.1 e.2 := (Finset.mem_filter.mp he).2
      have ha : normSq (D.spins n e.1) ≤ 1 := by
        simpa [Network.spins, hP.1] using spinVector_normSq_le_one (n ⟨e.1, hP.1⟩)
      have hb : normSq (D.spins n e.2) ≤ 1 := by
        simpa [Network.spins, hP.2.1] using spinVector_normSq_le_one (n ⟨e.2, hP.2.1⟩)
      exact factor_nonneg_of_ball _ _ ha hb
  · apply Finset.prod_nonneg
    intro e he
    split_ifs with hp
    · have hn : normSq (D.spins n e.val.1) ≤ 1 := by
        unfold Network.spins
        split_ifs with hactive
        · exact spinVector_normSq_le_one (n ⟨e.val.1, hactive⟩)
        · simp [normSq, dot]
      exact factor_nonneg_of_ball _ _ (le_of_eq (τ e).property) hn
    · norm_num

private def threePairSum (a b c : Vec3) : ℝ :=
  dot a b + dot a c + dot b c

private lemma threePairSum_lower (a b c : Vec3)
    (ha : normSq a ≤ 1) (hb : normSq b ≤ 1) (hc : normSq c ≤ 1) :
    -(3 / 2 : ℝ) ≤ threePairSum a b c := by
  have h := normSq_nonneg (a + b + c)
  rw [normSq_add_three] at h
  unfold threePairSum
  nlinarith

private def threePairObservable (f g o : Plane) (n : Plane → Vec3) : ℝ :=
  threePairSum (n f) (n g) (n o)

private lemma network_spin_ball {G : Finset Plane} (D : Network G)
    (n : (x : D.active) → SpinLetter) (x : Plane) :
    normSq (D.spins n x) ≤ 1 := by
  unfold Network.spins
  split_ifs with hx
  · exact spinVector_normSq_le_one (n ⟨x, hx⟩)
  · simp [normSq, dot]

private lemma partition_pair_bound {G : Finset Plane} (D : Network G)
    (τ : PinAssignment G) (pinned : Bool) (f g o : Plane) :
    0 ≤ D.partition τ pinned (fun n => threePairObservable f g o n) +
      (3 / 2 : ℝ) * D.partition τ pinned (fun _ => 1) := by
  have hsum : 0 ≤ ∑ n : (x : D.active) → SpinLetter,
      networkTermWeight D τ pinned n *
        (threePairSum (D.spins n f) (D.spins n g) (D.spins n o) + 3 / 2) := by
    apply Finset.sum_nonneg
    intro n hn
    apply mul_nonneg
    · exact network_weight_nonneg D τ pinned n
    · have h := threePairSum_lower (D.spins n f) (D.spins n g) (D.spins n o)
        (network_spin_ball D n f) (network_spin_ball D n g) (network_spin_ball D n o)
      linarith
  have heq : (∑ n : (x : D.active) → SpinLetter,
      networkTermWeight D τ pinned n *
        (threePairSum (D.spins n f) (D.spins n g) (D.spins n o) + 3 / 2)) =
      D.partition τ pinned (fun n => threePairObservable f g o n) +
        (3 / 2 : ℝ) * D.partition τ pinned (fun _ => 1) := by
    rw [network_partition_as_sum, network_partition_as_sum]
    simp only [threePairObservable]
    rw [Finset.mul_sum]
    simp only [mul_one]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    simp only [threePairSum]
    ring
  rw [← heq]
  exact hsum

private lemma partition_threePair_add {G : Finset Plane} (D : Network G)
    (τ : PinAssignment G) (pinned : Bool) (f g o : Plane) :
    D.partition τ pinned (fun n => threePairObservable f g o n) =
      D.partition τ pinned (fun n => dot (n f) (n g)) +
        D.partition τ pinned (fun n => dot (n f) (n o)) +
        D.partition τ pinned (fun n => dot (n g) (n o)) := by
  rw [network_partition_as_sum, network_partition_as_sum,
    network_partition_as_sum, network_partition_as_sum]
  simp only [threePairObservable]
  simp_rw [threePairSum, mul_add]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]

private lemma logarithmicMean_pos (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    0 < AKLT.Defs.logarithmicMean x y := by
  unfold AKLT.Defs.logarithmicMean
  by_cases heq : x = y
  · simpa [heq] using hx
  · rw [if_neg heq]
    rcases lt_trichotomy x y with hxy | hxy | hyx
    · have hlog := Real.log_lt_log hx hxy
      have hn : 0 < -(x - y) := by linarith
      have hd : 0 < -(Real.log x - Real.log y) := by linarith
      have hden : Real.log x - Real.log y < 0 := by linarith
      have hratio : (x - y) / (Real.log x - Real.log y) =
          (-(x - y)) / (-(Real.log x - Real.log y)) := by
        field_simp [ne_of_lt hden]
      rw [hratio]
      exact div_pos hn hd
    · exact (heq hxy).elim
    · have hlog := Real.log_lt_log hy hyx
      exact div_pos (by linarith) (by linarith)

private lemma responseI_pos {G : Finset Plane} (D : Network G)
    (τ : PinAssignment G) (pinned : Bool) (y o f g : Plane) :
    0 < responseI D τ pinned y o f g := by
  let E := removeSite D y
  let Z := E.partition τ pinned (fun _ => 1)
  have hZ : 0 ≤ Z := by
    change 0 ≤ E.partition τ pinned (fun _ => 1)
    rw [network_partition_as_sum]
    apply Finset.sum_nonneg
    intro n hn
    simpa only [mul_one] using network_weight_nonneg E τ pinned n
  by_cases hZ0 : Z = 0
  · simp [responseI, removedPairMean, Network.expectation, E, Z, hZ0]
  · have hZpos : 0 < Z := lt_of_le_of_ne hZ (Ne.symm hZ0)
    have hbound := partition_pair_bound E τ pinned f g o
    have hsum := partition_threePair_add E τ pinned f g o
    have hmeans : -(3 / 2 : ℝ) ≤
        removedPairMean D τ pinned y f g + removedPairMean D τ pinned y f o +
          removedPairMean D τ pinned y g o := by
      have hpair : -(3 / 2 : ℝ) ≤
          E.partition τ pinned (fun n => threePairObservable f g o n) / Z := by
        rw [hsum]
        apply (le_div_iff₀ hZpos).2
        linarith [hbound]
      change -(3 / 2 : ℝ) ≤
        E.expectation τ pinned (fun n => dot (n f) (n g)) +
          E.expectation τ pinned (fun n => dot (n f) (n o)) +
          E.expectation τ pinned (fun n => dot (n g) (n o))
      simp only [Network.expectation, Z]
      rw [← add_div, ← add_div]
      rw [← hsum]
      exact hpair
    unfold responseI
    linarith

end AKLT.W.REC020

theorem AKLT.W.REC020.main : AKLT.Blueprint.Rec.BetaPositiveStatement := by
  intro a hU f g hfg hof hog hdiff
  have ht := AKLT.W.REC020.responseI_pos a.D a.τ true a.y a.o f g
  have hf := AKLT.W.REC020.responseI_pos a.D a.τ false a.y a.o f g
  unfold AKLT.Defs.responseBeta
  apply div_pos
  · norm_num
  · exact mul_pos (by norm_num) (logarithmicMean_pos _ _ ht hf)

#print axioms AKLT.W.REC020.main
