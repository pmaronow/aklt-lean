import AKLT.W.REC095.Trace

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC095

theorem icoVector_normSq (j : IcoLetter) : normSq (icoVector j) = 1 := by
  have hs : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hphi : goldenRatio ^ 2 = goldenRatio + 1 := by
    unfold goldenRatio
    nlinarith
  have hp : 0 < goldenRatio + 2 := by
    unfold goldenRatio
    nlinarith [Real.sqrt_nonneg (5 : ℝ)]
  have hr : icoRadius ^ 2 = goldenRatio + 2 := Real.sq_sqrt hp.le
  have hr0 : icoRadius ≠ 0 := by
    have : 0 < icoRadius := Real.sqrt_pos.mpr hp
    exact this.ne'
  rcases j with ⟨r, a, b⟩
  fin_cases r <;> fin_cases a <;> fin_cases b <;>
    norm_num [icoVector, normSq, dot, Fin.sum_univ_succ, signValue] <;>
    field_simp <;> nlinarith

theorem normSq_nonneg (v : Vec3) : 0 ≤ normSq v := by
  unfold normSq dot
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)

theorem normSq_zero : normSq (0 : Vec3) = 0 := by simp [normSq, dot]

theorem dot_ge_neg_one {a b : Vec3} (ha : normSq a ≤ 1) (hb : normSq b ≤ 1) :
    -1 ≤ dot a b := by
  have hsum : normSq (a + b) = normSq a + 2 * dot a b + normSq b := by
    simp [normSq, dot, Fin.sum_univ_succ]
    ring
  have hp := normSq_nonneg (a + b)
  rw [hsum] at hp
  linarith

theorem spinVector_normSq_le (s : SpinLetter) : normSq (spinVector s) ≤ 1 := by
  cases s with
  | none => norm_num [spinVector, normSq_zero]
  | some j => exact (icoVector_normSq j).le

theorem spinWeight_nonneg (s : Status) (j : SpinLetter) : 0 ≤ spinWeight s j := by
  cases s <;> cases j <;> norm_num [spinWeight]

theorem spins_normSq_le {G : Finset Plane} (D : Network G)
    (σ : (x : D.active) → SpinLetter) (x : Plane) : normSq (D.spins σ x) ≤ 1 := by
  unfold Network.spins
  split_ifs
  · exact spinVector_normSq_le _
  · norm_num [normSq_zero]

/-- Nonnegativity needs no validity assumptions and handles zero normalizers. -/
theorem partition_nonneg {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) : 0 ≤ D.partition τ b (fun _ => 1) := by
  unfold Network.partition
  apply Finset.sum_nonneg
  intro σ hσ
  apply mul_nonneg
  · apply mul_nonneg
    · exact mul_nonneg (Finset.prod_nonneg fun x _ => spinWeight_nonneg _ _) (by norm_num)
    · apply Finset.prod_nonneg
      intro e he
      linarith [dot_ge_neg_one (spins_normSq_le D σ e.1) (spins_normSq_le D σ e.2)]
  · apply Finset.prod_nonneg
    intro e he
    split_ifs
    · linarith [dot_ge_neg_one (τ e).property.le (spins_normSq_le D σ e.val.1)]
    · norm_num

end AKLT.W.REC095
