import AKLT.Blueprint.Rec.NodesRenewal

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC084

theorem main : AKLT.Blueprint.Rec.RenewalActionStatement := by
  intro m h θ ρ hθ₀ hθ₁ hρ₀ hρ₁ hrows f hf X d
  rcases hf with ⟨B, hB⟩
  let w : PairType × ℕ → ℝ := fun j => m X j.1 j.2 * h j.1 * θ ^ (-(j.2 : ℤ))
  let g : PairType × ℕ → ℝ := fun j => m X j.1 j.2 * f j.1 (d - (j.2 : ℤ))
  have hBnonneg : 0 ≤ B := (hB .B 0).1.trans (hB .B 0).2
  have hhmin : 0 < AKLT.Blueprint.Rec.hmin h := by
    unfold AKLT.Blueprint.Rec.hmin
    exact lt_min (hrows.2.1 .B) (hrows.2.1 .C)
  have hratio : 0 ≤ B / AKLT.Blueprint.Rec.hmin h := div_nonneg hBnonneg hhmin.le
  have hweight : ∀ j : PairType × ℕ, 1 ≤ θ ^ (-(j.2 : ℤ)) := by
    intro j
    apply one_le_zpow_of_nonpos₀ hθ₀ hθ₁.le
    exact neg_nonpos.mpr (Int.natCast_nonneg j.2)
  have hmin_le : ∀ Y : PairType, AKLT.Blueprint.Rec.hmin h ≤ h Y := by
    intro Y
    cases Y with
    | B => exact min_le_left _ _
    | C => exact min_le_right _ _
  have hB_le : ∀ j : PairType × ℕ,
      B ≤ (B / AKLT.Blueprint.Rec.hmin h) * h j.1 * θ ^ (-(j.2 : ℤ)) := by
    intro j
    have hbase : B ≤ (B / AKLT.Blueprint.Rec.hmin h) * h j.1 := by
      calc
        B = (B / AKLT.Blueprint.Rec.hmin h) * AKLT.Blueprint.Rec.hmin h := by
          field_simp [ne_of_gt hhmin]
        _ ≤ (B / AKLT.Blueprint.Rec.hmin h) * h j.1 :=
          mul_le_mul_of_nonneg_left (hmin_le j.1) hratio
    calc
      B ≤ (B / AKLT.Blueprint.Rec.hmin h) * h j.1 := hbase
      _ ≤ ((B / AKLT.Blueprint.Rec.hmin h) * h j.1) * θ ^ (-(j.2 : ℤ)) :=
        le_mul_of_one_le_right
          (mul_nonneg hratio (hrows.2.1 j.1).le) (hweight j)
      _ = (B / AKLT.Blueprint.Rec.hmin h) * h j.1 * θ ^ (-(j.2 : ℤ)) := by ring
  have htarget_nonneg : ∀ j : PairType × ℕ, 0 ≤ g j := by
    intro j
    dsimp [g]
    exact mul_nonneg (hrows.1 X j.1 j.2) (hB j.1 (d - (j.2 : ℤ))).1
  have hmajor : ∀ j : PairType × ℕ, g j ≤ (B / AKLT.Blueprint.Rec.hmin h) * w j := by
    intro j
    dsimp [g, w]
    calc
      m X j.1 j.2 * f j.1 (d - (j.2 : ℤ)) ≤ m X j.1 j.2 * B :=
        mul_le_mul_of_nonneg_left (hB j.1 (d - (j.2 : ℤ))).2 (hrows.1 X j.1 j.2)
      _ ≤ m X j.1 j.2 *
          ((B / AKLT.Blueprint.Rec.hmin h) * h j.1 * θ ^ (-(j.2 : ℤ))) :=
        mul_le_mul_of_nonneg_left (hB_le j) (hrows.1 X j.1 j.2)
      _ = (B / AKLT.Blueprint.Rec.hmin h) * w j := by ring
  have hw : Summable w := by
    simpa [w] using hrows.2.2.1 X
  have hg : Summable g := by
    apply Summable.of_nonneg_of_le htarget_nonneg hmajor
    exact hw.mul_left (B / AKLT.Blueprint.Rec.hmin h)
  have hsum : Summable (fun j : PairType × ℕ => m X j.1 j.2 * f j.1 (d - (j.2 : ℤ))) := by
    simpa [g] using hg
  refine ⟨hsum, ?_⟩
  unfold AKLT.Blueprint.Rec.renewalOp
  apply tsum_nonneg
  intro j
  exact htarget_nonneg j

end AKLT.W.REC084
