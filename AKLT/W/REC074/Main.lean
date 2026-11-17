module
public import AKLT.Blueprint.Rec.NodesRecursion

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC074

private lemma goldenRatio_sq : goldenRatio ^ 2 = goldenRatio + 1 := by
  unfold goldenRatio
  have h : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  nlinarith [h]

private lemma icoVector_normSq (j : IcoLetter) : normSq (icoVector j) = 1 := by
  rcases j with ⟨k, a, b⟩
  have hp : 0 < goldenRatio + 2 := by
    unfold goldenRatio
    positivity
  have hr : icoRadius ^ 2 = goldenRatio + 2 := by
    unfold icoRadius
    exact Real.sq_sqrt hp.le
  fin_cases k <;> fin_cases a <;> fin_cases b <;>
    simp [icoVector, signValue, normSq, dot, Fin.sum_univ_succ] <;>
    (have hR : icoRadius ≠ 0 := ne_of_gt (by unfold icoRadius; exact Real.sqrt_pos.2 hp)
     field_simp [hR]
     nlinarith [goldenRatio_sq, hr])

private lemma spinVector_normSq_le_one (j : SpinLetter) : normSq (spinVector j) ≤ 1 := by
  cases j with
  | none => norm_num [spinVector, normSq, dot]
  | some j => simpa [spinVector] using (le_of_eq (icoVector_normSq j))

private lemma euclideanNorm_le_one (a : Vec3) (ha : normSq a ≤ 1) :
    ‖(WithLp.toLp 2 a : EuclideanSpace ℝ (Fin 3))‖ ≤ 1 := by
  rw [EuclideanSpace.norm_eq]
  simp only [Real.norm_eq_abs, sq_abs]
  apply Real.sqrt_le_one.mpr
  simpa [normSq, dot, pow_two] using ha

private lemma dot_abs_le_one (a b : Vec3) (ha : normSq a ≤ 1) (hb : normSq b ≤ 1) :
    |dot a b| ≤ 1 := by
  let x : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 a
  let y : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 b
  have hx : ‖x‖ ≤ 1 := euclideanNorm_le_one a ha
  have hy : ‖y‖ ≤ 1 := euclideanNorm_le_one b hb
  have hdot : dot a b = inner ℝ x y := by
    simp [x, y, dot, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]
  rw [hdot]
  calc
    |inner ℝ x y| ≤ ‖x‖ * ‖y‖ := abs_real_inner_le_norm _ _
    _ ≤ 1 := by nlinarith [norm_nonneg x, norm_nonneg y]

private lemma one_add_dot_nonneg (a b : Vec3) (ha : normSq a ≤ 1) (hb : normSq b ≤ 1) :
    0 ≤ 1 + dot a b := by
  have h := dot_abs_le_one a b ha hb
  have := (abs_le.mp h).1
  linarith

private def configurationWeight {G : Finset Plane} (D : Network G)
    (τ : PinAssignment G) (pinned : Bool) (n : (x : D.active) → SpinLetter) : ℝ :=
  (∏ x : D.active, spinWeight (D.status x.val) (n x)) *
    (∏ e ∈ D.bonds, (1 + dot (D.spins n e.1) (D.spins n e.2))) *
      ∏ e : originalLegs G,
        if pinned = true ∧ e.val.1 ∈ D.active then
          1 + dot (τ e).val (D.spins n e.val.1) else 1

private lemma active_status_cases {G : Finset Plane} (D : Network G) (x : D.active) :
    D.status x.val = .U ∨ D.status x.val = .D := by
  have hx : D.status x.val ≠ .X := by
    have hx' := x.property
    exact (Finset.mem_filter.mp hx').2
  cases h : D.status x.val <;> simp_all

private lemma spins_normSq_le_one {G : Finset Plane} (D : Network G)
    (n : (x : D.active) → SpinLetter) (x : Plane) (hx : x ∈ D.active) :
    normSq (D.spins n x) ≤ 1 := by
  simp [Network.spins, hx, spinVector_normSq_le_one]

private lemma configurationWeight_nonneg {G : Finset Plane} (D : Network G)
    (τ : PinAssignment G) (pinned : Bool)
    (n : (x : D.active) → SpinLetter) : 0 ≤ configurationWeight D τ pinned n := by
  unfold configurationWeight
  apply mul_nonneg
  · apply mul_nonneg
    · apply Finset.prod_nonneg
      intro x hx
      rcases active_status_cases D x with hU | hD'
      · rw [hU]
        cases n x <;> norm_num [spinWeight]
      · rw [hD']
        cases n x <;> norm_num [spinWeight]
    · apply Finset.prod_nonneg
      intro e he
      have hp : D.Present e.1 e.2 := (Finset.mem_filter.mp he).2
      exact one_add_dot_nonneg _ _
        (spins_normSq_le_one D n e.1 hp.1)
        (spins_normSq_le_one D n e.2 hp.2.1)
  · apply Finset.prod_nonneg
    intro e he
    by_cases hp : pinned = true ∧ e.val.1 ∈ D.active
    · simp [hp]
      exact one_add_dot_nonneg _ _
        (by
          have ht : normSq (τ e).val = 1 := (τ e).property
          linarith)
        (spins_normSq_le_one D n e.val.1 hp.2)
    · simp [hp]

private lemma network_partition_nonneg {G : Finset Plane} (D : Network G)
    (τ : PinAssignment G) (pinned : Bool) :
    0 ≤ D.partition τ pinned (fun _ => 1) := by
  unfold Network.partition
  apply Finset.sum_nonneg
  intro n hn
  simpa [configurationWeight, mul_assoc] using configurationWeight_nonneg D τ pinned n

private lemma abs_weighted_sum_le {ι : Type*} [Fintype ι] (w f : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hf : ∀ i, |f i| ≤ 1) :
    |∑ i, w i * f i| ≤ ∑ i, w i := by
  calc
    |∑ i, w i * f i| ≤ ∑ i, |w i * f i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, w i := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul, abs_of_nonneg (hw i)]
      simpa using mul_le_mul_of_nonneg_left (hf i) (hw i)

private lemma network_partition_observable_abs_le {G : Finset Plane} (D : Network G)
    (τ : PinAssignment G) (pinned : Bool)
    (f : (Plane → Vec3) → ℝ) (hf : ∀ n : (x : D.active) → SpinLetter,
      |f (D.spins n)| ≤ 1) :
    |D.partition τ pinned f| ≤ D.partition τ pinned (fun _ => 1) := by
  unfold Network.partition
  simp only [mul_one]
  have hsum : (∑ n : (x : D.active) → SpinLetter,
      ((∏ x : D.active, spinWeight (D.status x.val) (n x)) * f (D.spins n) *
        (∏ e ∈ D.bonds, (1 + dot (D.spins n e.1) (D.spins n e.2))) *
        (∏ e : originalLegs G, if pinned = true ∧ e.val.1 ∈ D.active then
          1 + dot (τ e).val (D.spins n e.val.1) else 1))) =
      ∑ n : (x : D.active) → SpinLetter, configurationWeight D τ pinned n * f (D.spins n) := by
    apply Finset.sum_congr rfl
    intro n hn
    simp [configurationWeight, mul_assoc, mul_left_comm, mul_comm]
  rw [hsum]
  change |∑ n : (x : D.active) → SpinLetter,
      configurationWeight D τ pinned n * f (D.spins n)| ≤
    ∑ n : (x : D.active) → SpinLetter, configurationWeight D τ pinned n
  apply abs_weighted_sum_le
  · exact configurationWeight_nonneg D τ pinned
  · exact hf

private lemma network_expectation_abs_le_one {G : Finset Plane} (D : Network G)
    (τ : PinAssignment G) (pinned : Bool)
    (f : (Plane → Vec3) → ℝ) (hf : ∀ n : (x : D.active) → SpinLetter,
      |f (D.spins n)| ≤ 1) : |D.expectation τ pinned f| ≤ 1 := by
  unfold Network.expectation
  change |D.partition τ pinned f / D.partition τ pinned (fun _ => 1)| ≤ 1
  have hz : 0 ≤ D.partition τ pinned (fun _ => 1) := network_partition_nonneg D τ pinned
  have hn : |D.partition τ pinned f| ≤ D.partition τ pinned (fun _ => 1) :=
    network_partition_observable_abs_le D τ pinned f hf
  by_cases hz0 : D.partition τ pinned (fun _ => 1) = 0
  · simp [hz0]
  · have hp : 0 < D.partition τ pinned (fun _ => 1) := lt_of_le_of_ne hz (Ne.symm hz0)
    rw [abs_div, abs_of_pos hp]
    exact div_le_one_of_le₀ hn (le_of_lt hp)

private lemma response_abs_le_two {G : Finset Plane} (D : Network G)
    (τ : PinAssignment G) (u v : Plane)
    (hu : u ∈ D.active) (hv : v ∈ D.active) (pinned : Bool) :
    |D.expectation τ pinned (fun n => dot (n u) (n v))| ≤ 1 := by
  apply network_expectation_abs_le_one D τ pinned
  intro n
  exact dot_abs_le_one (D.spins n u) (D.spins n v)
    (spins_normSq_le_one D n u hu) (spins_normSq_le_one D n v hv)

private lemma responseDifference_abs_le_two {G : Finset Plane} (D : Network G)
    (τ : PinAssignment G) (u v : Plane)
    (hu : u ∈ D.active) (hv : v ∈ D.active) :
    |D.expectation τ true (fun n => dot (n u) (n v)) -
      D.expectation τ false (fun n => dot (n u) (n v))| ≤ 2 := by
  have ht := response_abs_le_two D τ u v hu hv true
  have hf := response_abs_le_two D τ u v hu hv false
  have ht' := (abs_le.mp ht)
  have hf' := (abs_le.mp hf)
  rw [abs_le]
  constructor <;> linarith

private lemma responseEnvelope_class_bddAbove (X : PairType) (d : ℤ) :
    BddAbove ({0} ∪ {r : ℝ | ∃ G : Finset Plane, ∃ τ : PinAssignment G,
      ∃ D : Network G, ∃ u v c : Plane, D.ResponsePair X u v c ∧
      (d.toNat : ℕ∞) ≤ min (setDistance latticeDist u (↑(protectedSites G) : Set Plane))
        (setDistance latticeDist v (↑(protectedSites G) : Set Plane)) ∧
      r = |D.expectation τ true (fun n => dot (n u) (n v)) -
        D.expectation τ false (fun n => dot (n u) (n v))|}) := by
  refine ⟨2, ?_⟩
  intro r hr
  rcases hr with hr | ⟨G, τ, D, u, v, c, hPair, hdepth, rfl⟩
  · simp only [Set.mem_singleton_iff] at hr
    rw [hr]
    norm_num
  · rcases hPair with ⟨hCons, hu, hv, hc, hcx, huc, hvc, htype, huStatus, hvStatus⟩
    exact responseDifference_abs_le_two D τ u v hu hv

end AKLT.W.REC074

namespace AKLT.W.REC074

theorem main : AKLT.Blueprint.Rec.EnvelopeOrderStatement := by
  constructor
  · intro X d hd
    unfold AKLT.Defs.responseEnvelope
    have hnat : d.toNat = 0 := Int.toNat_of_nonpos (le_of_lt hd)
    simp [hnat]
  · intro X d₁ d₂ h12
    unfold AKLT.Defs.responseEnvelope
    apply csSup_le_csSup
    · exact responseEnvelope_class_bddAbove X d₁
    · exact Set.nonempty_of_mem (Set.mem_union_left _ (Set.mem_singleton 0))
    · intro r hr
      rcases hr with hr | ⟨G, τ, D, u, v, c, hPair, hdepth, rfl⟩
      · exact Set.mem_union_left _ hr
      · apply Set.mem_union_right
        refine ⟨G, τ, D, u, v, c, hPair, ?_, rfl⟩
        exact (Nat.cast_le.mpr (Int.toNat_le_toNat h12)) |>.trans hdepth

end AKLT.W.REC074
