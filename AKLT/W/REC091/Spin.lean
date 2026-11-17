module
public import AKLT.Defs.Response

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC091

theorem normSq_nonneg (v : Vec3) : 0 ≤ normSq v := by
  change 0 ≤ ∑ i : Fin 3, v i * v i
  exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (v i))

theorem dot_comm (a b : Vec3) : dot a b = dot b a := by
  unfold dot
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

theorem normSq_add (a b : Vec3) :
    normSq (a + b) = normSq a + 2 * dot a b + normSq b := by
  simp only [normSq, dot, Pi.add_apply, Fin.sum_univ_succ]
  ring

theorem normSq_sub (a b : Vec3) :
    normSq (a - b) = normSq a - 2 * dot a b + normSq b := by
  simp only [normSq, dot, Pi.sub_apply, Fin.sum_univ_succ]
  ring

theorem dot_bounds {a b : Vec3} (ha : normSq a ≤ 1) (hb : normSq b ≤ 1) :
    -1 ≤ dot a b ∧ dot a b ≤ 1 := by
  have hp := normSq_nonneg (a + b)
  have hm := normSq_nonneg (a - b)
  rw [normSq_add] at hp
  rw [normSq_sub] at hm
  constructor <;> linarith

theorem eq_neg_of_dot_eq_neg_one {a b : Vec3}
    (ha : normSq a ≤ 1) (hb : normSq b ≤ 1) (h : dot a b = -1) : a = -b := by
  have hzero : normSq (a + b) = 0 := by
    have hp := normSq_nonneg (a + b)
    rw [normSq_add, h] at hp ⊢
    linarith
  have hz : ∀ i : Fin 3, (a + b) i = 0 := by
    have hz' : ∑ i : Fin 3, ((a + b) i) ^ 2 = 0 := by
      simpa only [normSq, dot, pow_two] using hzero
    intro i
    have hi : ((a + b) i) ^ 2 ≤ ∑ j : Fin 3, ((a + b) j) ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    rw [hz'] at hi
    nlinarith [sq_nonneg ((a + b) i)]
  funext i
  have hi := hz i
  simpa only [Pi.add_apply, Pi.neg_apply] using (eq_neg_of_add_eq_zero_left hi)

theorem goldenRatio_pos : 0 < goldenRatio := by
  have h := Real.sqrt_nonneg (5 : ℝ)
  unfold goldenRatio
  positivity

theorem goldenRatio_gt_one : 1 < goldenRatio := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have hn := Real.sqrt_nonneg (5 : ℝ)
  unfold goldenRatio
  nlinarith

theorem goldenRatio_sq : goldenRatio ^ 2 = goldenRatio + 1 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  unfold goldenRatio
  nlinarith

theorem icoRadius_pos : 0 < icoRadius := by
  unfold icoRadius
  exact Real.sqrt_pos.mpr (by linarith [goldenRatio_pos])

theorem icoRadius_sq : icoRadius ^ 2 = goldenRatio + 2 :=
  Real.sq_sqrt (by linarith [goldenRatio_pos])

theorem ico_unit (j : IcoLetter) : normSq (icoVector j) = 1 := by
  have hr : icoRadius ≠ 0 := ne_of_gt icoRadius_pos
  have hg := goldenRatio_sq
  have hs := icoRadius_sq
  rcases j with ⟨a, b, c⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    norm_num [normSq, dot, icoVector, signValue, Fin.sum_univ_succ] <;>
    field_simp <;> nlinarith

theorem spin_ball (j : SpinLetter) : normSq (spinVector j) ≤ 1 := by
  cases j with
  | none => norm_num [spinVector, normSq, dot]
  | some j => exact (ico_unit j).le

theorem spinWeight_nonneg (s : Status) (j : SpinLetter) : 0 ≤ spinWeight s j := by
  cases s <;> cases j <;> norm_num [spinWeight]

theorem spinWeight_some_pos {s : Status} (hs : s ≠ .X) (j : IcoLetter) :
    0 < spinWeight s (some j) := by
  cases s <;> simp_all [spinWeight]

/-- Six distinct icosahedral atoms in one open half-space. Consequently every
pair of these atoms has a strictly positive bond factor. -/
def hemisphereLetter (j : Fin 3 × Fin 2) : IcoLetter := (j.1, j.2, 0)

def coordinateSum (v : Vec3) : ℝ := ∑ i, v i

theorem hemisphere_positive (j : Fin 3 × Fin 2) :
    0 < coordinateSum (icoVector (hemisphereLetter j)) := by
  have hg := goldenRatio_gt_one
  have hr := icoRadius_pos
  have hd : 1 / icoRadius < goldenRatio / icoRadius :=
    (div_lt_div_iff_of_pos_right hr).mpr hg
  simp only [one_div] at hd
  rcases j with ⟨a, b⟩
  fin_cases a <;> fin_cases b <;>
    norm_num [coordinateSum, hemisphereLetter, icoVector, signValue,
      Fin.sum_univ_succ, neg_div, one_div] <;> linarith [inv_pos.mpr hr]

theorem hemisphere_injective : Function.Injective (icoVector ∘ hemisphereLetter) := by
  have hr : icoRadius ≠ 0 := ne_of_gt icoRadius_pos
  have hg : goldenRatio ≠ 0 := ne_of_gt goldenRatio_pos
  rintro ⟨a, b⟩ ⟨c, d⟩ he
  have h0 := congrFun he 0
  have h1 := congrFun he 1
  have h2 := congrFun he 2
  clear he
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    first
    | rfl
    | (norm_num [Function.comp_def, hemisphereLetter, icoVector, signValue,
        div_left_inj' hr, hg, hr, neg_div, one_div] at * <;>
        linarith [inv_pos.mpr icoRadius_pos])

theorem hemisphere_bond_pos (i j : Fin 3 × Fin 2) :
    0 < 1 + dot (icoVector (hemisphereLetter i)) (icoVector (hemisphereLetter j)) := by
  have hi := ico_unit (hemisphereLetter i)
  have hj := ico_unit (hemisphereLetter j)
  have hn := (dot_bounds hi.le hj.le).1
  have hp := hemisphere_positive i
  have hq := hemisphere_positive j
  apply lt_of_le_of_ne (by linarith : 0 ≤ 1 + dot _ _) ?_
  intro he
  have hd : dot (icoVector (hemisphereLetter i)) (icoVector (hemisphereLetter j)) = -1 :=
    by linarith
  have hv := eq_neg_of_dot_eq_neg_one hi.le hj.le hd
  have hz := congrArg coordinateSum hv
  have hneg (v : Vec3) : coordinateSum (-v) = -coordinateSum v := by
    simp only [coordinateSum, Pi.neg_apply, Finset.sum_neg_distrib]
  rw [hneg] at hz
  linarith

end AKLT.W.REC091
