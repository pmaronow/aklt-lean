module
public import AKLT.Blueprint.Rec.NodesResponse

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC013

theorem golden_pos : 0 < goldenRatio := by
  unfold goldenRatio
  positivity

theorem golden_sq : goldenRatio ^ 2 = goldenRatio + 1 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  unfold goldenRatio
  nlinarith

theorem radius_pos : 0 < icoRadius := by
  unfold icoRadius
  exact Real.sqrt_pos.2 (by linarith [golden_pos])

theorem radius_sq : icoRadius ^ 2 = goldenRatio + 2 := by
  exact Real.sq_sqrt (by linarith [golden_pos])

theorem ico_unit (j : IcoLetter) : normSq (icoVector j) = 1 := by
  rcases j with ⟨a,b,c⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    norm_num [normSq, dot, icoVector, signValue, Fin.sum_univ_succ] <;>
    field_simp [ne_of_gt radius_pos] <;> nlinarith [golden_sq, radius_sq]

theorem spin_ball (j : SpinLetter) : normSq (spinVector j) ≤ 1 := by
  cases j with
  | none => norm_num [normSq, dot, spinVector]
  | some j => exact (ico_unit j).le

theorem dot_comm (v w : Vec3) : dot v w = dot w v := by
  unfold dot
  congr 1
  funext i
  ring

theorem factor_nonneg (v w : Vec3) (hv : normSq v ≤ 1) (hw : normSq w ≤ 1) :
    0 ≤ 1 + dot v w := by
  simp [normSq, dot, Fin.sum_univ_succ] at *
  nlinarith [sq_nonneg (v 0 + w 0), sq_nonneg (v 1 + w 1),
    sq_nonneg (v 2 + w 2)]

theorem factor_zero (v w : Vec3) (hv : normSq v = 1) (hw : normSq w = 1)
    (h : 1 + dot v w = 0) : v = -w := by
  simp [normSq, dot, Fin.sum_univ_succ] at hv hw h
  have hsum : ∑ k : Fin 3, (v k + w k) ^ 2 = 0 := by
    simp [Fin.sum_univ_succ]
    nlinarith only [hv, hw, h]
  funext i
  have hi : (v i + w i) ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg (v k + w k))).mp hsum i
      (Finset.mem_univ i)
  have hz := (sq_eq_zero_iff).1 hi
  change v i = -w i
  linarith

/-- Six unit atoms, chosen with no antipodal pair. -/
def candidate (j : Fin 3 × Fin 2) : IcoLetter := (j.1, 0, j.2)

theorem candidate_injective : Function.Injective (fun j => icoVector (candidate j)) := by
  rintro ⟨a,b⟩ ⟨c,d⟩ h
  have hr := ne_of_gt radius_pos
  have hg := ne_of_gt golden_pos
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  clear h
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d
  all_goals try rfl
  all_goals try norm_num [candidate, icoVector, signValue, hr, hg] at h0
  all_goals try norm_num [candidate, icoVector, signValue, hr, hg] at h1
  all_goals try norm_num [candidate, icoVector, signValue, hr, hg] at h2
  all_goals nlinarith [golden_pos, div_pos golden_pos radius_pos, inv_pos.mpr radius_pos]

theorem candidate_not_antipodal (a b : Fin 3 × Fin 2) :
    icoVector (candidate a) ≠ -icoVector (candidate b) := by
  intro h
  rcases a with ⟨a,e⟩
  rcases b with ⟨c,d⟩
  have hr := ne_of_gt radius_pos
  have hg := ne_of_gt golden_pos
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  clear h
  fin_cases a <;> fin_cases e <;> fin_cases c <;> fin_cases d
  all_goals try norm_num [candidate, icoVector, signValue, hr, hg] at h0
  all_goals try norm_num [candidate, icoVector, signValue, hr, hg] at h1
  all_goals try norm_num [candidate, icoVector, signValue, hr, hg] at h2
  all_goals nlinarith [golden_pos, div_pos golden_pos radius_pos, inv_pos.mpr radius_pos]

theorem candidate_factor_pos (a b : Fin 3 × Fin 2) :
    0 < 1 + dot (icoVector (candidate a)) (icoVector (candidate b)) := by
  refine lt_of_le_of_ne (factor_nonneg _ _ (ico_unit _).le (ico_unit _).le) ?_
  intro h
  exact candidate_not_antipodal a b (factor_zero _ _ (ico_unit _) (ico_unit _) h.symm)

/-- The only moment needed at a one-bond D departure. -/
theorem d_integral_one (v : Vec3) :
    ∑ j : SpinLetter, spinWeight .D j * (1 + dot (spinVector j) v) = 1 := by
  norm_num [Fintype.sum_option, Fintype.sum_prod_type, Fin.sum_univ_succ,
    spinWeight, spinVector, icoVector, signValue, dot] <;> ring

end AKLT.W.REC013
