module
public import AKLT.Defs.Domain

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC010

theorem golden_pos : 0 < goldenRatio := by
  unfold goldenRatio
  positivity

theorem golden_sq : goldenRatio ^ 2 = goldenRatio + 1 := by
  have hs : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  unfold goldenRatio
  nlinarith

theorem radius_pos : 0 < icoRadius := by
  unfold icoRadius
  exact Real.sqrt_pos.mpr (by linarith [golden_pos])

theorem radius_sq : icoRadius ^ 2 = goldenRatio + 2 := by
  exact Real.sq_sqrt (by linarith [golden_pos])

/-- Every geometric atom of the actual site support is a unit vector. -/
theorem ico_unit (j : IcoLetter) : normSq (icoVector j) = 1 := by
  rcases j with ⟨j, a, b⟩
  fin_cases j <;> fin_cases a <;> fin_cases b <;>
    norm_num [icoVector, signValue, normSq, dot, Fin.sum_univ_succ] <;>
    field_simp [ne_of_gt radius_pos] <;>
    nlinarith [golden_sq, radius_sq]

theorem normSq_nonneg (a : Vec3) : 0 ≤ normSq a := by
  change 0 ≤ ∑ i, a i * a i
  exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (a i))

theorem normSq_add (a b : Vec3) :
    normSq (a + b) = normSq a + normSq b + 2 * dot a b := by
  change (a + b) ⬝ᵥ (a + b) = a ⬝ᵥ a + b ⬝ᵥ b + 2 * (a ⬝ᵥ b)
  rw [add_dotProduct, dotProduct_add, dotProduct_add, dotProduct_comm b a]
  ring

theorem dot_comm (a b : Vec3) : dot a b = dot b a := dotProduct_comm a b

/-- All interaction factors on the closed unit ball are nonnegative. -/
theorem factor_nonneg {a b : Vec3} (ha : normSq a ≤ 1) (hb : normSq b ≤ 1) :
    0 ≤ 1 + dot a b := by
  have h := normSq_nonneg (a + b)
  rw [normSq_add] at h
  linarith

/-- A unit atom can have a zero factor with a ball field only at its antipode. -/
theorem eq_neg_of_factor_zero {a b : Vec3} (ha : normSq a = 1)
    (hb : normSq b ≤ 1) (h : 1 + dot a b = 0) : a = -b := by
  have hzero : normSq (a + b) = 0 := by
    have hn := normSq_nonneg (a + b)
    rw [normSq_add] at hn ⊢
    linarith
  have heq : a + b = 0 := dotProduct_self_eq_zero.mp hzero
  exact eq_neg_of_add_eq_zero_left heq

/-- Six unit atoms, one from each antipodal pair. -/
abbrev HalfLetter := Fin 3 × Fin 2

def halfLetter (j : HalfLetter) : IcoLetter := (j.1, 0, j.2)

def halfVector (j : HalfLetter) : Vec3 := icoVector (halfLetter j)

theorem half_unit (j : HalfLetter) : normSq (halfVector j) = 1 :=
  ico_unit (halfLetter j)

theorem half_injective : Function.Injective halfVector := by
  intro ⟨a, s⟩ ⟨b, t⟩ h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  fin_cases a <;> fin_cases s <;> fin_cases b <;> fin_cases t <;>
    norm_num [halfVector, halfLetter, icoVector, signValue] at h0 h1 h2 ⊢ <;>
    (try field_simp [ne_of_gt radius_pos] at h0) <;>
    (try field_simp [ne_of_gt radius_pos] at h1) <;>
    (try field_simp [ne_of_gt radius_pos] at h2) <;>
    linarith [golden_pos, radius_pos]

theorem half_ne_neg (a b : HalfLetter) : halfVector a ≠ -halfVector b := by
  intro h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  rcases a with ⟨a, s⟩
  rcases b with ⟨b, t⟩
  fin_cases a <;> fin_cases s <;> fin_cases b <;> fin_cases t <;>
    norm_num [halfVector, halfLetter, icoVector, signValue] at h0 h1 h2 <;>
    (try field_simp [ne_of_gt radius_pos] at h0) <;>
    (try field_simp [ne_of_gt radius_pos] at h1) <;>
    (try field_simp [ne_of_gt radius_pos] at h2) <;>
    linarith [golden_pos, radius_pos]

theorem half_pair_pos (a b : HalfLetter) : 0 < 1 + dot (halfVector a) (halfVector b) := by
  have hn := factor_nonneg (half_unit a).le (half_unit b).le
  exact lt_of_le_of_ne hn (fun h => half_ne_neg a b
    (eq_neg_of_factor_zero (half_unit a) (half_unit b).le h.symm))

end AKLT.W.REC010
