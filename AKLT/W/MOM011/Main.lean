import AKLT.Blueprint.Mom.NodesFinite

open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.MOM011

theorem main : AKLT.Blueprint.Mom.BallDotBoundsStatement := by
  intro a b ha hb
  have ha0 : 0 ≤ normSq a := by
    simp only [normSq, dot]
    exact Finset.sum_nonneg fun i hi => mul_self_nonneg (a i)
  have hb0 : 0 ≤ normSq b := by
    simp only [normSq, dot]
    exact Finset.sum_nonneg fun i hi => mul_self_nonneg (b i)
  have hcs : dot a b ^ 2 ≤ normSq a * normSq b := by
    simpa [dot, normSq, pow_two] using
      (Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 3)) a b)
  have hprod : normSq a * normSq b ≤ 1 := by
    calc
      normSq a * normSq b ≤ 1 * normSq b := mul_le_mul_of_nonneg_right ha hb0
      _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hb (by norm_num)
      _ = 1 := by norm_num
  have hdot : dot a b ^ 2 ≤ 1 := le_trans hcs hprod
  have hlow : -1 ≤ dot a b := by
    nlinarith [sq_nonneg (dot a b + 1)]
  have hhigh : dot a b ≤ 1 := by
    nlinarith [sq_nonneg (dot a b - 1)]
  constructor <;> nlinarith

end AKLT.W.MOM011
