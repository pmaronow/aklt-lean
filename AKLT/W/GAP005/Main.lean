module
public import AKLT.Blueprint.Gap.NodesFinite

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Gap

namespace AKLT.W.GAP005

theorem main : AKLT.Blueprint.Gap.CouplingMarginalTVStatement := by
  classical
  intro Ω Ξ hΩ hΞ p q hp hq
  constructor
  · intro c
    have hdiagP (x : Ω) : c.mass x x ≤ p x := by
      rw [← c.first_marginal x]
      exact Finset.single_le_sum (fun y hy => c.nonnegative x y) (Finset.mem_univ x)
    have hdiagQ (x : Ω) : c.mass x x ≤ q x := by
      rw [← c.second_marginal x]
      exact Finset.single_le_sum (fun y hy => c.nonnegative y x) (Finset.mem_univ x)
    have hpoint (x : Ω) :
        |p x - q x| ≤ p x + q x - 2 * c.mass x x := by
      exact abs_sub_le_iff.mpr ⟨by linarith [hdiagQ x], by linarith [hdiagP x]⟩
    have hsum :
        (∑ x, |p x - q x|) ≤ ∑ x, (p x + q x - 2 * c.mass x x) :=
      Finset.sum_le_sum (fun x _ => hpoint x)
    have hdiagRow (x : Ω) :
        (∑ y, if x = y then 0 else c.mass x y) = p x - c.mass x x := by
      calc
        (∑ y, if x = y then 0 else c.mass x y) =
            ∑ y, (c.mass x y - if x = y then c.mass x y else 0) := by
          apply Finset.sum_congr rfl
          intro y hy
          by_cases h : x = y <;> simp [h]
        _ = (∑ y, c.mass x y) - ∑ y, if x = y then c.mass x y else 0 :=
          by rw [Finset.sum_sub_distrib]
        _ = p x - c.mass x x := by simp [c.first_marginal]
    have hoffdiag :
        (∑ x, ∑ y, if x = y then 0 else c.mass x y) =
          1 - ∑ x, c.mass x x := by
      calc
        (∑ x, ∑ y, if x = y then 0 else c.mass x y) =
            ∑ x, (p x - c.mass x x) := by
          apply Finset.sum_congr rfl
          intro x hx
          exact hdiagRow x
        _ = (∑ x, p x) - ∑ x, c.mass x x := by rw [Finset.sum_sub_distrib]
        _ = 1 - ∑ x, c.mass x x := by rw [hp.2]
    have hbound :
        (1 / 2 : ℝ) * ∑ x, |p x - q x| ≤
          (1 / 2 : ℝ) * ∑ x, (p x + q x - 2 * c.mass x x) :=
      mul_le_mul_of_nonneg_left hsum (by norm_num)
    unfold totalVariation
    calc
      (1 / 2 : ℝ) * ∑ x, |p x - q x| ≤
          (1 / 2 : ℝ) * ∑ x, (p x + q x - 2 * c.mass x x) := hbound
      _ = 1 - ∑ x, c.mass x x := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hp.2, hq.2]
        rw [← Finset.mul_sum]
        ring
      _ = ∑ x, ∑ y, if x = y then 0 else c.mass x y := hoffdiag.symm
  · intro r
    have hpush (z : Ξ) :
        |marginal p r z - marginal q r z| ≤
          ∑ x, if r x = z then |p x - q x| else 0 := by
      have hdiff : marginal p r z - marginal q r z =
          ∑ x, if r x = z then p x - q x else 0 := by
        calc
          marginal p r z - marginal q r z =
              (∑ x, if r x = z then p x else 0) -
                ∑ x, if r x = z then q x else 0 := rfl
          _ = ∑ x, ((if r x = z then p x else 0) -
                (if r x = z then q x else 0)) := by rw [← Finset.sum_sub_distrib]
          _ = ∑ x, if r x = z then p x - q x else 0 := by
            apply Finset.sum_congr rfl
            intro x hx
            by_cases h : r x = z <;> simp [h]
      rw [hdiff]
      calc
        |∑ x, if r x = z then p x - q x else 0| ≤
            ∑ x, |if r x = z then p x - q x else 0| :=
          Finset.abs_sum_le_sum_abs _ _
        _ = ∑ x, if r x = z then |p x - q x| else 0 := by
          apply Finset.sum_congr rfl
          intro x hx
          by_cases h : r x = z <;> simp [h]
    have hsum :
        (∑ z, |marginal p r z - marginal q r z|) ≤
          ∑ z, ∑ x, if r x = z then |p x - q x| else 0 :=
      Finset.sum_le_sum (s := Finset.univ) (fun z hz => hpush z)
    unfold totalVariation
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    calc
      (∑ z, |marginal p r z - marginal q r z|) ≤
          ∑ z, ∑ x, if r x = z then |p x - q x| else 0 := hsum
      _ = ∑ x, ∑ z, if r x = z then |p x - q x| else 0 := Finset.sum_comm
      _ = ∑ x, |p x - q x| := by
        apply Finset.sum_congr rfl
        intro x hx
        simp

end AKLT.W.GAP005

