import AKLT.Blueprint.Mom.NodesMean

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Mom

namespace AKLT.W.MOM022

private theorem split_identity (a e : Vec3) (t : ℝ)
    (hcoord : ∀ i, a i = (2 * t - 1) * e i) :
    ∀ v : Vec3, 1 + dot v a =
      t * (1 + dot v e) + (1 - t) * (1 + dot v (-e)) := by
  intro v
  have hdot : dot v a = (2 * t - 1) * dot v e := by
    change (∑ i, v i * a i) = _
    simp_rw [hcoord]
    calc
      (∑ i, v i * ((2 * t - 1) * e i)) =
          ∑ i, (2 * t - 1) * (v i * e i) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = (2 * t - 1) * ∑ i, v i * e i := (Finset.mul_sum _ _ _).symm
  have hneg : dot v (-e) = -dot v e := by
    simp [dot]
  rw [hdot, hneg]
  ring

theorem main : AKLT.Blueprint.Mom.BallFieldSplitStatement := by
  intro a ha
  let n : ℝ := normSq a
  have hn : 0 ≤ n := by
    dsimp [n, normSq, dot]
    rw [Fin.sum_univ_three]
    nlinarith [sq_nonneg (a 0), sq_nonneg (a 1), sq_nonneg (a 2)]
  have hnle : n ≤ 1 := ha
  by_cases hr : 0 < Real.sqrt n
  · let r : ℝ := Real.sqrt n
    let t : ℝ := (1 + r) / 2
    let eVal : Vec3 := fun i => a i / r
    have hrpos : 0 < r := by simpa [r] using hr
    have hrnonneg : 0 ≤ r := le_of_lt hrpos
    have hr2 : r ^ 2 = n := by
      dsimp [r]
      exact Real.sq_sqrt hn
    have hrle : r ≤ 1 := by
      dsimp [r]
      exact Real.sqrt_le_one.mpr hnle
    have ht0 : 0 ≤ t := by dsimp [t]; linarith
    have ht1 : t ≤ 1 := by dsimp [t]; linarith
    have hscale (c : ℝ) (x : Vec3) : normSq (fun i => c * x i) = c ^ 2 * normSq x := by
      unfold normSq dot
      calc
        (∑ i, (c * x i) * (c * x i)) = ∑ i, (c * c) * (x i * x i) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = (c * c) * ∑ i, x i * x i := (Finset.mul_sum _ _ _).symm
        _ = c ^ 2 * ∑ i, x i * x i := by ring
    have heunit : normSq eVal = 1 := by
      have hfun : eVal = fun i => (1 / r) * a i := by
        funext i
        dsimp [eVal]
        field_simp
      rw [hfun, hscale]
      have hrne : r ≠ 0 := ne_of_gt hrpos
      dsimp [n] at hr2
      field_simp
      nlinarith [hr2]
    let e : UnitVector := ⟨eVal, heunit⟩
    have hcoord : ∀ i, a i = (2 * t - 1) * e.val i := by
      intro i
      dsimp [e, eVal, t]
      field_simp [ne_of_gt hrpos]
      ring
    refine ⟨t, e, ht0, ht1, ?_⟩
    exact split_identity a e.val t hcoord
  · have hroot : Real.sqrt n = 0 := by
      have hnonneg : 0 ≤ Real.sqrt n := Real.sqrt_nonneg n
      exact le_antisymm (le_of_not_gt hr) hnonneg
    have hnzero : n = 0 := by
      have hs := Real.sq_sqrt hn
      rw [hroot] at hs
      simpa using hs.symm
    have hsum : a 0 * a 0 + a 1 * a 1 + a 2 * a 2 = 0 := by
      dsimp [n, normSq, dot] at hnzero
      simpa [Fin.sum_univ_three] using hnzero
    have ha0sq : a 0 * a 0 = 0 := by nlinarith [sq_nonneg (a 1), sq_nonneg (a 2)]
    have ha1sq : a 1 * a 1 = 0 := by nlinarith [sq_nonneg (a 0), sq_nonneg (a 2)]
    have ha2sq : a 2 * a 2 = 0 := by nlinarith [sq_nonneg (a 0), sq_nonneg (a 1)]
    have ha0 : a 0 = 0 := mul_self_eq_zero.mp ha0sq
    have ha1 : a 1 = 0 := mul_self_eq_zero.mp ha1sq
    have ha2 : a 2 = 0 := mul_self_eq_zero.mp ha2sq
    let eVal : Vec3 := fun i => if i = 0 then 1 else 0
    have heunit : normSq eVal = 1 := by
      norm_num [eVal, normSq, dot, Fin.sum_univ_three]
    let e : UnitVector := ⟨eVal, heunit⟩
    have hcoord : ∀ i, a i = (2 * (1 / 2 : ℝ) - 1) * e.val i := by
      intro i
      fin_cases i <;> simp [e, eVal, ha0, ha1, ha2]
    refine ⟨1 / 2, e, by norm_num, by norm_num, ?_⟩
    exact split_identity a e.val (1 / 2) hcoord

end AKLT.W.MOM022
