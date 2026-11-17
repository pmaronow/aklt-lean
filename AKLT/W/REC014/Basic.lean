module
public import AKLT.Blueprint.Rec.NodesResponse

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC014

theorem dot_comm (a b : Vec3) : dot a b = dot b a := by
  unfold dot
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem normSq_nonneg (a : Vec3) : 0 ≤ normSq a := by
  change 0 ≤ ∑ i, a i * a i
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg (a i)

theorem normSq_add (a b : Vec3) :
    normSq (a + b) = normSq a + normSq b + 2 * dot a b := by
  simp only [normSq, dot, Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib]
  rw [show (∑ i, b i * a i) = ∑ i, a i * b i by
    apply Finset.sum_congr rfl; intro i _; ring]
  ring

theorem factor_nonneg (a b : Vec3) (ha : normSq a ≤ 1) (hb : normSq b ≤ 1) :
    0 ≤ 1 + dot a b := by
  have h := normSq_nonneg (a + b)
  rw [normSq_add] at h
  linarith

theorem normSq_eq_zero {a : Vec3} (h : normSq a = 0) : a = 0 := by
  funext i
  have hi : a i * a i ≤ normSq a :=
    Finset.single_le_sum (fun j _ => mul_self_nonneg (a j)) (Finset.mem_univ i)
  rw [h] at hi
  simpa using (mul_self_eq_zero.mp (le_antisymm hi (mul_self_nonneg (a i))))

theorem factor_pos (a b : Vec3) (ha : normSq a ≤ 1) (hb : normSq b ≤ 1)
    (hne : a ≠ -b) : 0 < 1 + dot a b := by
  have h := factor_nonneg a b ha hb
  apply lt_of_le_of_ne h
  intro he
  have hz : normSq (a + b) = 0 := by
    rw [normSq_add]
    have := normSq_nonneg (a + b)
    rw [normSq_add] at this
    linarith
  have := normSq_eq_zero hz
  exact hne (eq_neg_of_add_eq_zero_left this)

theorem golden_square : goldenRatio ^ 2 = goldenRatio + 1 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  unfold goldenRatio
  nlinarith

theorem radius_pos : 0 < icoRadius := by
  apply Real.sqrt_pos.2
  unfold goldenRatio
  positivity

theorem radius_square : icoRadius ^ 2 = goldenRatio + 2 := by
  apply Real.sq_sqrt
  unfold goldenRatio
  positivity

theorem ico_unit (j : IcoLetter) : normSq (icoVector j) = 1 := by
  rcases j with ⟨a, b, c⟩
  have hr := radius_square
  have hp := golden_square
  have hn := ne_of_gt radius_pos
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp [normSq, dot, icoVector, signValue, Fin.sum_univ_succ] <;>
    field_simp <;> nlinarith

theorem spin_ball (j : SpinLetter) : normSq (spinVector j) ≤ 1 := by
  cases j with
  | none => simp [spinVector, normSq, dot]
  | some j => exact le_of_eq (ico_unit j)

theorem weight_nonneg (s : Status) (j : SpinLetter) : 0 ≤ spinWeight s j := by
  cases s <;> cases j <;> norm_num [spinWeight]

theorem weight_pos (s : Status) (hs : s ≠ .X) (j : IcoLetter) :
    0 < spinWeight s (some j) := by
  cases s <;> norm_num [spinWeight] at *

theorem weight_sum (s : Status) (hs : s ≠ .X) : ∑ j, spinWeight s j = 1 := by
  cases s <;> norm_num [spinWeight, Fintype.sum_option, IcoLetter,
    Fintype.card_prod] at *

theorem weighted_dot_zero (v : Vec3) :
    ∑ j, spinWeight .U j * dot (spinVector j) v = 0 := by
  simp [Fintype.sum_option, spinWeight, spinVector, dot, icoVector, signValue,
    Fintype.sum_prod_type, Fin.sum_univ_succ]
  ring

theorem weighted_factor_one (v : Vec3) :
    ∑ j, spinWeight .U j * (1 + dot (spinVector j) v) = 1 := by
  simp_rw [mul_add, mul_one, Finset.sum_add_distrib]
  rw [weight_sum .U (by decide), weighted_dot_zero, add_zero]

/-- Six unit atoms, with no antipodal pair. -/
def label (j : Fin 3 × Fin 2) : IcoLetter := (j.1, 0, j.2)

theorem label_injective : Function.Injective (fun j => icoVector (label j)) := by
  intro ⟨a,b⟩ ⟨c,d⟩ h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  clear h
  have hp : 0 < goldenRatio := by unfold goldenRatio; positivity
  have hr := ne_of_gt radius_pos
  have hri : 0 < icoRadius⁻¹ := inv_pos.mpr radius_pos
  have hpi : 0 < goldenRatio / icoRadius := div_pos hp radius_pos
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [label, icoVector, signValue, hr, ne_of_gt hp, neg_div] at h0 <;>
    simp [label, icoVector, signValue, hr, ne_of_gt hp, neg_div] at h1 <;>
    simp [label, icoVector, signValue, hr, ne_of_gt hp, neg_div] at h2 <;>
    first | rfl | linarith

theorem label_not_antipodal (j k : Fin 3 × Fin 2) :
    icoVector (label j) ≠ -icoVector (label k) := by
  rcases j with ⟨a,b⟩
  rcases k with ⟨c,d⟩
  intro h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  clear h
  have hp : 0 < goldenRatio := by unfold goldenRatio; positivity
  have hr := ne_of_gt radius_pos
  have hri : 0 < icoRadius⁻¹ := inv_pos.mpr radius_pos
  have hpi : 0 < goldenRatio / icoRadius := div_pos hp radius_pos
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [label, icoVector, signValue, hr, ne_of_gt hp, neg_div] at h0 <;>
    simp [label, icoVector, signValue, hr, ne_of_gt hp, neg_div] at h1 <;>
    simp [label, icoVector, signValue, hr, neg_div] at h2 <;> linarith

theorem label_avoids {ι : Type*} [Fintype ι] (b : ι → UnitVector)
    (hc : Fintype.card ι ≤ 4) :
    ∃ j : Fin 3 × Fin 2, ∀ i, 0 < 1 + dot (icoVector (label j)) (b i).val := by
  classical
  let bad (i : ι) := Finset.univ.filter fun j : Fin 3 × Fin 2 =>
    ¬ 0 < 1 + dot (icoVector (label j)) (b i).val
  have hb (i : ι) : (bad i).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro j hj k hk
    apply label_injective
    have he (l) (hl : l ∈ bad i) : icoVector (label l) = -(b i).val := by
      by_contra h
      exact (Finset.mem_filter.mp hl).2
        (factor_pos _ _ (le_of_eq (ico_unit _)) (le_of_eq (b i).property) h)
    exact (he j hj).trans (he k hk).symm
  have hcard : (Finset.univ.biUnion bad).card ≤ 4 := by
    calc
      _ ≤ ∑ i, (bad i).card := Finset.card_biUnion_le
      _ ≤ ∑ _ : ι, 1 := Finset.sum_le_sum fun i _ => hb i
      _ = Fintype.card ι := by simp
      _ ≤ 4 := hc
  have hlt : (Finset.univ.biUnion bad).card <
      (Finset.univ : Finset (Fin 3 × Fin 2)).card := by
    simpa using (show (Finset.univ.biUnion bad).card < 6 by omega)
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  refine ⟨j, fun i => ?_⟩
  by_contra hn
  exact hj (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, hn⟩⟩)

end AKLT.W.REC014
