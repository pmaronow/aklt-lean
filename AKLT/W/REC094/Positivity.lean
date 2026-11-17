module
public import AKLT.Defs.Domain

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC094

theorem goldenRatio_pos : 0 < goldenRatio := by
  unfold goldenRatio
  positivity

theorem goldenRatio_sq : goldenRatio ^ 2 = goldenRatio + 1 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  dsimp [goldenRatio]
  nlinarith

theorem icoRadius_pos : 0 < icoRadius := by
  unfold icoRadius
  exact Real.sqrt_pos.2 (by linarith [goldenRatio_pos])

theorem icoVector_unit (j : IcoLetter) : normSq (icoVector j) = 1 := by
  have hr : icoRadius ≠ 0 := ne_of_gt icoRadius_pos
  have hrs : icoRadius ^ 2 = goldenRatio + 2 :=
    Real.sq_sqrt (by linarith [goldenRatio_pos])
  rcases j with ⟨a, b, c⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp [normSq, dot, icoVector, signValue, Fin.sum_univ_succ] <;>
    field_simp <;> nlinarith [goldenRatio_sq]

theorem normSq_nonneg (v : Vec3) : 0 ≤ normSq v := by
  unfold normSq dot
  exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (v i))

theorem normSq_eq_zero_iff (v : Vec3) : normSq v = 0 ↔ v = 0 := by
  constructor
  · intro h
    change (∑ i, v i * v i) = 0 at h
    have hi : ∀ i, v i * v i = 0 :=
      fun i => (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => mul_self_nonneg (v j))).1 h i (Finset.mem_univ i)
    funext i
    exact (mul_self_eq_zero.mp (hi i))
  · rintro rfl
    simp [normSq, dot]

theorem dot_comm (a b : Vec3) : dot a b = dot b a := by
  simp [dot, mul_comm]

theorem normSq_add (a b : Vec3) :
    normSq (a + b) = normSq a + normSq b + 2 * dot a b := by
  simp only [normSq, dot, Pi.add_apply]
  simp_rw [show ∀ i, (a i + b i) * (a i + b i) =
    a i * a i + b i * b i + 2 * (a i * b i) by intro i; ring]
  simp [Finset.sum_add_distrib, Finset.mul_sum]

theorem one_add_dot_nonneg (a b : Vec3) (ha : normSq a ≤ 1) (hb : normSq b ≤ 1) :
    0 ≤ 1 + dot a b := by
  have h := normSq_nonneg (a + b)
  rw [normSq_add] at h
  linarith

theorem one_add_dot_pos (a b : Vec3) (ha : normSq a = 1) (hb : normSq b = 1)
    (hne : a ≠ -b) : 0 < 1 + dot a b := by
  have hp : 0 < normSq (a + b) := by
    apply lt_of_le_of_ne (normSq_nonneg _)
    intro hz
    have he := (normSq_eq_zero_iff (a + b)).1 hz.symm
    exact hne (eq_neg_of_add_eq_zero_left he)
  rw [normSq_add, ha, hb] at hp
  linarith

/-- Six icosahedron letters containing no antipodal pair. -/
def positiveLetters : Finset IcoLetter :=
  Finset.univ.filter fun j => j.2.1 = 0

theorem positiveLetters_card : positiveLetters.card = 6 := by decide +kernel

theorem positiveLetters_injective : Set.InjOn icoVector (↑positiveLetters : Set IcoLetter) := by
  intro j hj k hk he
  have hj0 : j.2.1 = 0 := (Finset.mem_filter.mp hj).2
  have hk0 : k.2.1 = 0 := (Finset.mem_filter.mp hk).2
  rcases j with ⟨a, b, c⟩
  rcases k with ⟨d, e, f⟩
  dsimp at hj0 hk0
  subst b; subst e
  have hr := ne_of_gt icoRadius_pos
  have hg := ne_of_gt goldenRatio_pos
  have he0 := congrArg (fun v : Vec3 => v 0 * icoRadius) he
  have he1 := congrArg (fun v : Vec3 => v 1 * icoRadius) he
  have he2 := congrArg (fun v : Vec3 => v 2 * icoRadius) he
  clear he hj hk
  fin_cases a <;> fin_cases c <;> fin_cases d <;> fin_cases f <;>
    try rfl
  all_goals
    simp [icoVector, signValue, hr, neg_mul] at he0 he1 he2 <;>
      exfalso <;> nlinarith [goldenRatio_pos]

theorem positiveLetters_not_antipodal (j : IcoLetter) (hj : j ∈ positiveLetters)
    (k : IcoLetter) (hk : k ∈ positiveLetters) : icoVector j ≠ -icoVector k := by
  have hj0 : j.2.1 = 0 := (Finset.mem_filter.mp hj).2
  have hk0 : k.2.1 = 0 := (Finset.mem_filter.mp hk).2
  rcases j with ⟨a, b, c⟩
  rcases k with ⟨d, e, f⟩
  dsimp at hj0 hk0
  subst b; subst e
  intro he
  have hr := ne_of_gt icoRadius_pos
  have hg := ne_of_gt goldenRatio_pos
  have he0 := congrArg (fun v : Vec3 => v 0 * icoRadius) he
  have he1 := congrArg (fun v : Vec3 => v 1 * icoRadius) he
  have he2 := congrArg (fun v : Vec3 => v 2 * icoRadius) he
  clear he hj hk
  fin_cases a <;> fin_cases c <;> fin_cases d <;> fin_cases f
  all_goals
    simp [icoVector, signValue, hr, neg_mul] at he0 he1 he2 <;>
      nlinarith [goldenRatio_pos]

theorem originalLeg_mem {G : Finset Plane} {e : Plane × Plane}
    (he : e ∈ originalLegs G) : e.1 ∈ G ∧ e.2 ∈ neighbours e.1 ∧ e.2 ∉ G := by
  rcases Finset.mem_biUnion.mp he with ⟨x, hx, he⟩
  rcases Finset.mem_image.mp he with ⟨z, hz, rfl⟩
  exact ⟨hx, (Finset.mem_sdiff.mp hz).1, (Finset.mem_sdiff.mp hz).2⟩

theorem originalLegs_at_card_le (G : Finset Plane) (x : Plane) :
    (Finset.univ.filter fun e : originalLegs G => e.val.1 = x).card ≤ 4 := by
  classical
  let s := Finset.univ.filter fun e : originalLegs G => e.val.1 = x
  have hc : s.card ≤ (neighbours x).card := by
    apply Finset.card_le_card_of_injOn (fun e : originalLegs G => e.val.2)
    · intro e he
      have heq := (Finset.mem_filter.mp he).2
      change e.val.2 ∈ neighbours x
      simpa only [heq] using (originalLeg_mem e.property).2.1
    · intro e he f hf hef
      apply Subtype.ext
      apply Prod.ext
      · exact (Finset.mem_filter.mp he).2.trans (Finset.mem_filter.mp hf).2.symm
      · exact hef
  have hn : (neighbours x).card ≤ 4 := by
    exact le_trans Finset.card_image_le (by decide)
  exact hc.trans hn

theorem exists_positive_letter (G : Finset Plane) (τ : PinAssignment G) (x : Plane) :
    ∃ j ∈ positiveLetters, ∀ e : originalLegs G,
      e.val.1 = x → icoVector j ≠ -(τ e).val := by
  classical
  let s := Finset.univ.filter fun e : originalLegs G => e.val.1 = x
  suffices ∃ j ∈ positiveLetters, ∀ e ∈ s, icoVector j ≠ -(τ e).val by
    obtain ⟨j, hj, he⟩ := this
    exact ⟨j, hj, fun e heq => he e (Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq⟩)⟩
  by_contra h
  push Not at h
  have hsub : positiveLetters.image icoVector ⊆ s.image (fun e => -(τ e).val) := by
    intro v hv
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨e, he, hj⟩ := h j hj
    exact Finset.mem_image.mpr ⟨e, he, hj.symm⟩
  have hc : positiveLetters.card ≤ s.card := by
    calc
      positiveLetters.card = (positiveLetters.image icoVector).card :=
        (Finset.card_image_of_injOn positiveLetters_injective).symm
      _ ≤ (s.image (fun e => -(τ e).val)).card := Finset.card_le_card hsub
      _ ≤ s.card := Finset.card_image_le
  have hs : s.card ≤ 4 := originalLegs_at_card_le G x
  rw [positiveLetters_card] at hc
  omega

theorem spinVector_normSq_le (j : SpinLetter) : normSq (spinVector j) ≤ 1 := by
  cases j with
  | none => norm_num [spinVector, normSq, dot]
  | some j => exact (icoVector_unit j).le

theorem spinWeight_nonneg (s : Status) (j : SpinLetter) : 0 ≤ spinWeight s j := by
  cases s <;> cases j <;> norm_num [spinWeight]

theorem Network.spins_normSq_le {G : Finset Plane} (D : Network G)
    (n : (x : D.active) → SpinLetter) (x : Plane) : normSq (D.spins n x) ≤ 1 := by
  unfold AKLT.Defs.Network.spins
  split_ifs
  · exact spinVector_normSq_le _
  · norm_num [normSq, dot]

theorem partition_nonneg {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) : 0 ≤ D.partition τ b (fun _ => 1) := by
  classical
  apply Finset.sum_nonneg
  intro σ _
  apply mul_nonneg
  · apply mul_nonneg
    · apply mul_nonneg
      · exact Finset.prod_nonneg (fun x _ => spinWeight_nonneg _ _)
      · norm_num
    · apply Finset.prod_nonneg
      intro e _
      exact one_add_dot_nonneg _ _ (Network.spins_normSq_le _ _ _)
        (Network.spins_normSq_le _ _ _)
  · apply Finset.prod_nonneg
    intro e _
    split_ifs
    · exact one_add_dot_nonneg _ _ (τ e).property.le (Network.spins_normSq_le _ _ _)
    · norm_num

/-- Positivity needs no closure or admissibility assumption: the present bonds
are lattice bonds and every original leg is counted at most once. -/
theorem partition_pos {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) : 0 < D.partition τ b (fun _ => 1) := by
  classical
  choose j hj hpin using exists_positive_letter G τ
  let σ : (x : D.active) → SpinLetter := fun x => some (j x.val)
  have hspin (x : Plane) (hx : x ∈ D.active) : D.spins σ x = icoVector (j x) := by
    simp [AKLT.Defs.Network.spins, hx, σ, spinVector]
  have hs (x : D.active) : 0 < spinWeight (D.status x.val) (σ x) := by
    have hne : D.status x.val ≠ .X := (Finset.mem_filter.mp x.property).2
    cases heq : D.status x.val <;> simp_all [σ, spinWeight]
  have hb (e : Plane × Plane) (he : e ∈ D.bonds) :
      0 < 1 + dot (D.spins σ e.1) (D.spins σ e.2) := by
    have hp := (Finset.mem_filter.mp he).2
    rw [hspin e.1 hp.1, hspin e.2 hp.2.1]
    exact one_add_dot_pos _ _ (icoVector_unit _) (icoVector_unit _)
      (positiveLetters_not_antipodal _ (hj _) _ (hj _))
  have hl (e : originalLegs G) :
      0 < (if b = true ∧ e.val.1 ∈ D.active then
        1 + dot (τ e).val (D.spins σ e.val.1) else 1) := by
    split_ifs with h
    · rw [hspin _ h.2, dot_comm]
      exact one_add_dot_pos _ _ (icoVector_unit _) (τ e).property (hpin _ e rfl)
    · norm_num
  have hw : 0 <
      (∏ x : D.active, spinWeight (D.status x.val) (σ x)) * 1 *
      (∏ e ∈ D.bonds, (1 + dot (D.spins σ e.1) (D.spins σ e.2))) *
      (∏ e : originalLegs G,
        if b = true ∧ e.val.1 ∈ D.active then
          1 + dot (τ e).val (D.spins σ e.val.1) else 1) := by
    exact mul_pos (mul_pos (mul_pos (Finset.prod_pos (fun x _ => hs x)) (by norm_num))
      (Finset.prod_pos hb)) (Finset.prod_pos (fun e _ => hl e))
  unfold AKLT.Defs.Network.partition
  apply Finset.sum_pos'
  · intro n _
    apply mul_nonneg
    · apply mul_nonneg
      · exact mul_nonneg (Finset.prod_nonneg (fun x _ => spinWeight_nonneg _ _))
          (by norm_num)
      · exact Finset.prod_nonneg (fun e _ => one_add_dot_nonneg _ _
          (Network.spins_normSq_le _ _ _) (Network.spins_normSq_le _ _ _))
    · apply Finset.prod_nonneg
      intro e _
      split_ifs
      · exact one_add_dot_nonneg _ _ (τ e).property.le (Network.spins_normSq_le _ _ _)
      · norm_num
  · exact ⟨σ, Finset.mem_univ _, hw⟩

#print axioms partition_pos

end AKLT.W.REC094
