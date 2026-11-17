module
public import AKLT.Blueprint.Gap.NodesFinite

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
set_option maxHeartbeats 800000
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Gap
attribute [local instance] Classical.propDecidable

namespace AKLT.W.GAP004

local instance (Ω : Type) : DecidableEq Ω := Classical.decEq Ω

private def overlap {Ω : Type} [Fintype Ω] (p q : Weight Ω) : ℝ :=
  ∑ x, min (p x) (q x)

private def leftResidual {Ω : Type} [Fintype Ω] (p q : Weight Ω) (x : Ω) : ℝ :=
  p x - min (p x) (q x)

private def rightResidual {Ω : Type} [Fintype Ω] (p q : Weight Ω) (x : Ω) : ℝ :=
  q x - min (p x) (q x)

private theorem abs_sub_eq_sum_mins (Ω : Type) [Fintype Ω] (p q : Weight Ω)
    (hp : Probability p) (hq : Probability q) :
    totalVariation p q = 1 - overlap p q := by
  have hpoint : ∀ x, |p x - q x| = p x + q x - 2 * min (p x) (q x) := by
    intro x
    rcases le_total (p x) (q x) with h | h
    · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
      ring
    · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
      ring
  unfold totalVariation overlap
  rw [Finset.sum_congr rfl (fun x _ => hpoint x), Finset.sum_sub_distrib,
    Finset.sum_add_distrib, hp.2, hq.2]
  rw [← Finset.mul_sum]
  norm_num
  ring

private theorem overlap_bounds (Ω : Type) [Fintype Ω] (p q : Weight Ω)
    (hp : Probability p) (hq : Probability q) :
    0 ≤ overlap p q ∧ overlap p q ≤ 1 := by
  constructor
  · unfold overlap
    exact Finset.sum_nonneg fun x _ => le_min (hp.1 x) (hq.1 x)
  · unfold overlap
    calc
      (∑ x, min (p x) (q x)) ≤ ∑ x, p x :=
        Finset.sum_le_sum fun x _ => min_le_left _ _
      _ = 1 := hp.2

private theorem residual_sums (Ω : Type) [Fintype Ω] (p q : Weight Ω)
    (hp : Probability p) (hq : Probability q) :
    (∑ x, leftResidual p q x) = 1 - overlap p q ∧
      (∑ x, rightResidual p q x) = 1 - overlap p q := by
  constructor
  · simp only [leftResidual]
    rw [Finset.sum_sub_distrib, hp.2]
    rfl
  · simp only [rightResidual]
    rw [Finset.sum_sub_distrib, hq.2]
    rfl

private theorem residual_nonneg (Ω : Type) [Fintype Ω] (p q : Weight Ω)
    (x : Ω) :
    0 ≤ leftResidual p q x ∧ 0 ≤ rightResidual p q x := by
  constructor
  · unfold leftResidual
    exact sub_nonneg.mpr (min_le_left _ _)
  · unfold rightResidual
    exact sub_nonneg.mpr (min_le_right _ _)

private theorem residual_product_diag_zero (Ω : Type) [Fintype Ω]
    (p q : Weight Ω) (x : Ω) :
    leftResidual p q x * rightResidual p q x = 0 := by
  unfold leftResidual rightResidual
  rcases le_total (p x) (q x) with h | h
  · rw [min_eq_left h]
    ring
  · rw [min_eq_right h]
    ring

private theorem overlap_one_eq (Ω : Type) [Fintype Ω] (p q : Weight Ω)
    (hp : Probability p) (hq : Probability q) (ht : overlap p q = 1) :
    ∀ x, p x = q x := by
  have hrs := residual_sums Ω p q hp hq
  have hleftsum : (∑ x, leftResidual p q x) = 0 := by rw [hrs.1, ht]; ring
  have hrightsum : (∑ x, rightResidual p q x) = 0 := by rw [hrs.2, ht]; ring
  intro x
  have hl := residual_nonneg Ω p q x |>.1
  have hr := residual_nonneg Ω p q x |>.2
  have hleleft : leftResidual p q x ≤ 0 :=
    (Finset.single_le_sum (s := Finset.univ)
      (f := leftResidual p q) (fun y _ => residual_nonneg Ω p q y |>.1)
      (Finset.mem_univ x)).trans_eq hleftsum
  have hleright : rightResidual p q x ≤ 0 :=
    (Finset.single_le_sum (s := Finset.univ)
      (f := rightResidual p q) (fun y _ => residual_nonneg Ω p q y |>.2)
      (Finset.mem_univ x)).trans_eq hrightsum
  have hleft : leftResidual p q x = 0 := le_antisymm hleleft hl
  have hright : rightResidual p q x = 0 := le_antisymm hleright hr
  have hpmin : min (p x) (q x) = p x := by
    unfold leftResidual at hleft
    linarith
  have hqmin : min (p x) (q x) = q x := by
    unfold rightResidual at hright
    linarith
  exact hpmin.symm.trans hqmin

private def diagonalCoupling {Ω : Type} [Fintype Ω] (p : Weight Ω)
    (hp : Probability p) : Coupling p p where
  mass x y := if x = y then p x else 0
  nonnegative x y := by
    split_ifs with h
    · exact hp.1 x
    · exact le_rfl
  first_marginal x := by simp
  second_marginal y := by simp [eq_comm]

private def residualCoupling {Ω : Type} [Fintype Ω] (p q : Weight Ω)
    (hp : Probability p) (hq : Probability q)
    (ht : overlap p q < 1) : Coupling p q := by
  classical
  have hden : 0 < 1 - overlap p q := sub_pos.mpr ht
  have hrs := residual_sums Ω p q hp hq
  exact {
    mass := fun x y => (if x = y then min (p x) (q x) else 0) +
      leftResidual p q x * rightResidual p q y / (1 - overlap p q)
    nonnegative := by
      intro x y
      apply add_nonneg
      · split_ifs with h
        · exact le_min (hp.1 x) (hq.1 x)
        · exact le_rfl
      · exact div_nonneg (mul_nonneg (residual_nonneg Ω p q x).1
          (residual_nonneg Ω p q y).2) hden.le
    first_marginal := by
      intro x
      rw [Finset.sum_add_distrib]
      have hdiag : (∑ y, if x = y then min (p x) (q x) else 0) =
          min (p x) (q x) := by simp
      have hres : (∑ y, leftResidual p q x * rightResidual p q y /
          (1 - overlap p q)) =
          leftResidual p q x := by
        calc
          _ = (∑ y, leftResidual p q x * rightResidual p q y) / (1 - overlap p q) := by
            rw [Finset.sum_div]
          _ = (leftResidual p q x * ∑ y, rightResidual p q y) /
              (1 - overlap p q) := by
            rw [Finset.mul_sum]
          _ = leftResidual p q x := by rw [hrs.2]; field_simp
      rw [hdiag, hres]
      unfold leftResidual
      ring
    second_marginal := by
      intro y
      rw [Finset.sum_add_distrib]
      have hdiag : (∑ x, if x = y then min (p x) (q x) else 0) =
          min (p y) (q y) := by simp
      have hres : (∑ x, leftResidual p q x * rightResidual p q y / (1 - overlap p q)) =
          rightResidual p q y := by
        calc
          _ = (∑ x, leftResidual p q x * rightResidual p q y) / (1 - overlap p q) := by
            rw [Finset.sum_div]
          _ = ((∑ x, leftResidual p q x) * rightResidual p q y) /
              (1 - overlap p q) := by
            rw [Finset.sum_mul]
          _ = rightResidual p q y := by rw [hrs.1]; field_simp
      rw [hdiag, hres]
      unfold rightResidual
      ring
  }

private theorem residualCoupling_disagreement {Ω : Type} [Fintype Ω]
    (p q : Weight Ω) (hp : Probability p) (hq : Probability q)
    (ht : overlap p q < 1) :
    (∑ x, ∑ y, if x = y then 0 else
      (residualCoupling p q hp hq ht).mass x y) = 1 - overlap p q := by
  have hden : 0 < 1 - overlap p q := sub_pos.mpr ht
  have hrs := residual_sums Ω p q hp hq
  have hpoint : ∀ x y, (if x = y then 0 else
      (residualCoupling p q hp hq ht).mass x y) =
      leftResidual p q x * rightResidual p q y / (1 - overlap p q) := by
    intro x y
    by_cases hxy : x = y
    · subst y
      have hd := residual_product_diag_zero Ω p q x
      simp [hd]
    · simp [hxy, residualCoupling]
  have hrow : ∀ x, (∑ y, if x = y then 0 else
      (residualCoupling p q hp hq ht).mass x y) = leftResidual p q x := by
    intro x
    calc
      _ = ∑ y, leftResidual p q x * rightResidual p q y /
          (1 - overlap p q) := by
        apply Finset.sum_congr rfl
        intro y hy
        exact hpoint x y
      _ = (leftResidual p q x * ∑ y, rightResidual p q y) /
          (1 - overlap p q) := by
        rw [Finset.mul_sum, Finset.sum_div]
      _ = leftResidual p q x := by
        rw [hrs.2]
        field_simp [ne_of_gt hden]
  calc
    (∑ x, ∑ y, if x = y then 0 else
        (residualCoupling p q hp hq ht).mass x y) =
        ∑ x, leftResidual p q x := by
      apply Finset.sum_congr rfl
      intro x hx
      exact hrow x
    _ = 1 - overlap p q := hrs.1

theorem main : AKLT.Blueprint.Gap.MaximalCouplingStatement := by
  unfold AKLT.Blueprint.Gap.MaximalCouplingStatement
  intro Ω inst p q hp hq
  have htv := abs_sub_eq_sum_mins Ω p q hp hq
  have hbounds := overlap_bounds Ω p q hp hq
  constructor
  · exact htv
  · rcases lt_or_eq_of_le hbounds.2 with hlt | heq
    · exact ⟨residualCoupling p q hp hq hlt,
        (residualCoupling_disagreement p q hp hq hlt).trans htv.symm⟩
    · have hpq := overlap_one_eq Ω p q hp hq heq
      have hpeq : p = q := funext hpq
      subst q
      refine ⟨diagonalCoupling p hp, ?_⟩
      calc
        (∑ x, ∑ y, if x = y then 0 else (diagonalCoupling p hp).mass x y) = 0 := by
          apply Finset.sum_eq_zero
          intro x hx
          apply Finset.sum_eq_zero
          intro y hy
          by_cases hxy : x = y
          · simp [hxy]
          · simp [hxy, diagonalCoupling]
        _ = totalVariation p p := by simp [totalVariation]

end AKLT.W.GAP004
