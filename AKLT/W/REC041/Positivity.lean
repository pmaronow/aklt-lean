module
public import AKLT.Defs.Domain

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC041

private theorem golden_pos : 0 < goldenRatio := by
  unfold goldenRatio
  positivity

private theorem golden_sq : goldenRatio ^ 2 = goldenRatio + 1 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  unfold goldenRatio
  nlinarith

private theorem radius_pos : 0 < icoRadius := by
  unfold icoRadius
  exact Real.sqrt_pos.2 (by linarith [golden_pos])

private theorem radius_sq : icoRadius ^ 2 = goldenRatio + 2 :=
  Real.sq_sqrt (by linarith [golden_pos])

theorem ico_unit (j : IcoLetter) : normSq (icoVector j) = 1 := by
  have hr : icoRadius ≠ 0 := ne_of_gt radius_pos
  rcases j with ⟨a, b, c⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp [normSq, dot, Fin.sum_univ_succ, icoVector, signValue] <;>
    field_simp <;> nlinarith [golden_sq, radius_sq]

private theorem normSq_nonneg (a : Vec3) : 0 ≤ normSq a := by
  change 0 ≤ ∑ i, a i * a i
  exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (a i))

private theorem normSq_add (a b : Vec3) :
    normSq (a + b) = normSq a + 2 * dot a b + normSq b := by
  simp only [normSq, dot, Pi.add_apply, Fin.sum_univ_succ]
  ring

theorem factor_nonneg (a b : Vec3) (ha : normSq a ≤ 1) (hb : normSq b ≤ 1) :
    0 ≤ 1 + dot a b := by
  have h := normSq_nonneg (a + b)
  rw [normSq_add] at h
  linarith

private theorem eq_neg_of_factor_zero (a b : Vec3)
    (ha : normSq a = 1) (hb : normSq b = 1) (h : 1 + dot a b = 0) :
    b = -a := by
  have hz : normSq (a + b) = 0 := by rw [normSq_add, ha, hb]; linarith
  have hi (i : Fin 3) : (a i + b i) * (a i + b i) = 0 := by
    have hsum : ∑ j : Fin 3, (a j + b j) * (a j + b j) = 0 := hz
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => mul_self_nonneg (a j + b j))).mp hsum i (Finset.mem_univ i)
  funext i
  have hh := mul_self_eq_zero.mp (hi i)
  simpa only [Pi.neg_apply] using (show b i = -a i by linarith)

/-- Six atoms with no antipodal pair. This leaves room for all four original pins. -/
abbrev HalfLetter := Fin 3 × Fin 2

def halfVector (j : HalfLetter) : Vec3 := icoVector (j.1, 0, j.2)

private theorem half_injective : Function.Injective halfVector := by
  intro i j h
  have hr : icoRadius ≠ 0 := ne_of_gt radius_pos
  have hg : goldenRatio ≠ 0 := ne_of_gt golden_pos
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  clear h
  rcases i with ⟨a, b⟩
  rcases j with ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [halfVector, icoVector, signValue] at h0 h1 h2 ⊢ <;>
    (try field_simp [hr] at h0) <;> (try field_simp [hr] at h1) <;>
    (try field_simp [hr] at h2) <;> simp_all <;> linarith [golden_pos]

private theorem half_not_antipodal (i j : HalfLetter) : halfVector j ≠ -halfVector i := by
  have hr : icoRadius ≠ 0 := ne_of_gt radius_pos
  have hg : goldenRatio ≠ 0 := ne_of_gt golden_pos
  intro h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  clear h
  rcases i with ⟨a, b⟩
  rcases j with ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [halfVector, icoVector, signValue] at h0 h1 h2 <;>
    (try field_simp [hr] at h0) <;> (try field_simp [hr] at h1) <;>
    (try field_simp [hr] at h2) <;> linarith [golden_pos, radius_pos]

theorem half_factor_pos (i j : HalfLetter) : 0 < 1 + dot (halfVector i) (halfVector j) := by
  have hi := ico_unit (i.1, 0, i.2)
  have hj := ico_unit (j.1, 0, j.2)
  refine lt_of_le_of_ne (factor_nonneg _ _ hi.le hj.le) ?_
  intro h
  exact half_not_antipodal i j (eq_neg_of_factor_zero _ _ hi hj h.symm)

private def siteLegs (G : Finset Plane) (x : Plane) : Finset (originalLegs G) :=
  Finset.univ.filter fun e => e.val.1 = x

private theorem leg_snd_mem {G : Finset Plane} {e : Plane × Plane}
    (he : e ∈ originalLegs G) : e.2 ∈ neighbours e.1 := by
  obtain ⟨x, _, he⟩ := Finset.mem_biUnion.mp he
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp he
  exact (Finset.mem_sdiff.mp hz).1

private theorem siteLegs_card_le (G : Finset Plane) (x : Plane) :
    (siteLegs G x).card ≤ 4 := by
  have hc : (siteLegs G x).card ≤ (neighbours x).card := by
    apply Finset.card_le_card_of_injOn (fun e : originalLegs G => e.val.2)
    · intro e he
      have hx := (Finset.mem_filter.mp he).2
      change e.val.2 ∈ neighbours x
      simpa only [hx] using leg_snd_mem e.property
    · intro e he f hf hh
      apply Subtype.ext
      apply Prod.ext
      · exact (Finset.mem_filter.mp he).2.trans (Finset.mem_filter.mp hf).2.symm
      · exact hh
  have hn : (neighbours x).card ≤ 4 := by
    exact (Finset.card_image_le).trans (by decide)
  omega

private theorem half_pin_choice {G : Finset Plane} (τ : PinAssignment G) (x : Plane) :
    ∃ j : HalfLetter, ∀ e : originalLegs G, e.val.1 = x →
      0 < 1 + dot (τ e).val (halfVector j) := by
  classical
  let bad (e : originalLegs G) : Finset HalfLetter :=
    Finset.univ.filter fun j => 1 + dot (τ e).val (halfVector j) = 0
  have hbad (e : originalLegs G) : (bad e).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    have hi' := (Finset.mem_filter.mp hi).2
    have hj' := (Finset.mem_filter.mp hj).2
    apply half_injective
    exact (eq_neg_of_factor_zero _ _ (τ e).property (ico_unit _) hi').trans
      (eq_neg_of_factor_zero _ _ (τ e).property (ico_unit _) hj').symm
  have hcard : ((siteLegs G x).biUnion bad).card < (Finset.univ : Finset HalfLetter).card := by
    have hc := Finset.card_biUnion_le_card_mul (siteLegs G x) bad 1 (fun e _ => hbad e)
    have hp := siteLegs_card_le G x
    have hu : (Finset.univ : Finset HalfLetter).card = 6 := by decide
    omega
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  refine ⟨j, ?_⟩
  intro e he
  have hne : 1 + dot (τ e).val (halfVector j) ≠ 0 := by
    intro h
    apply hj
    exact Finset.mem_biUnion.mpr ⟨e, by simp [siteLegs, he], by simp [bad, h]⟩
  exact lt_of_le_of_ne (factor_nonneg _ _ (τ e).property.le (ico_unit _).le) hne.symm

private theorem spin_ball (j : SpinLetter) : normSq (spinVector j) ≤ 1 := by
  cases j with
  | none => norm_num [spinVector, normSq, dot]
  | some j => exact (ico_unit j).le

private theorem spins_ball {G : Finset Plane} (D : Network G)
    (n : (x : D.active) → SpinLetter) (x : Plane) : normSq (D.spins n x) ≤ 1 := by
  unfold Network.spins
  split
  · exact spin_ball _
  · norm_num [normSq, dot]

private theorem mass_nonneg (s : Status) (j : SpinLetter) : 0 ≤ spinWeight s j := by
  cases s <;> cases j <;> norm_num [spinWeight]

private theorem mass_pos (s : Status) (hs : s ≠ .X) (j : IcoLetter) :
    0 < spinWeight s (some j) := by
  cases s <;> simp_all [spinWeight]

private def partitionWeight {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (n : (x : D.active) → SpinLetter) : ℝ :=
  (∏ x : D.active, spinWeight (D.status x.val) (n x)) *
    (∏ e ∈ D.bonds, (1 + dot (D.spins n e.1) (D.spins n e.2))) *
    ∏ e : originalLegs G,
      if b = true ∧ e.val.1 ∈ D.active then
        1 + dot (τ e).val (D.spins n e.val.1) else 1

private theorem partitionWeight_nonneg {G : Finset Plane} (D : Network G)
    (τ : PinAssignment G) (b : Bool) (n : (x : D.active) → SpinLetter) :
    0 ≤ partitionWeight D τ b n := by
  apply mul_nonneg
  · apply mul_nonneg
    · exact Finset.prod_nonneg (fun x _ => mass_nonneg _ _)
    · exact Finset.prod_nonneg (fun e _ => factor_nonneg _ _ (spins_ball D n _) (spins_ball D n _))
  · apply Finset.prod_nonneg
    intro e _
    split_ifs
    · exact factor_nonneg _ _ (τ e).property.le (spins_ball D n _)
    · norm_num

/-- The original leg slots alone number at most four at each site. Choose
independently from the six non-antipodal atoms, avoiding those pins. -/
theorem network_partition_pos {G : Finset Plane} (D : Network G)
    (τ : PinAssignment G) (b : Bool) : 0 < D.partition τ b (fun _ => 1) := by
  classical
  choose σ hσ using fun x : D.active => half_pin_choice τ x.val
  let n : (x : D.active) → SpinLetter := fun x => some ((σ x).1, 0, (σ x).2)
  have hn (x : D.active) : D.spins n x.val = halfVector (σ x) := by
    simp [Network.spins, n, spinVector, halfVector]
  have hw : 0 < partitionWeight D τ b n := by
    apply mul_pos
    · apply mul_pos
      · apply Finset.prod_pos
        intro x _
        exact mass_pos _ (Finset.mem_filter.mp x.property).2 _
      · apply Finset.prod_pos
        intro e he
        have hp : D.Present e.1 e.2 := (Finset.mem_filter.mp he).2
        rw [hn ⟨e.1, hp.1⟩, hn ⟨e.2, hp.2.1⟩]
        exact half_factor_pos _ _
    · apply Finset.prod_pos
      intro e _
      split_ifs with he
      · rw [hn ⟨e.val.1, he.2⟩]
        exact hσ ⟨e.val.1, he.2⟩ e rfl
      · norm_num
  have hsum : D.partition τ b (fun _ => 1) = ∑ m, partitionWeight D τ b m := by
    simp [Network.partition, partitionWeight]
  rw [hsum]
  exact Finset.sum_pos' (fun m _ => partitionWeight_nonneg D τ b m)
    ⟨n, Finset.mem_univ _, hw⟩

#print axioms ico_unit
#print axioms factor_nonneg
#print axioms half_factor_pos
#print axioms network_partition_pos

end AKLT.W.REC041
