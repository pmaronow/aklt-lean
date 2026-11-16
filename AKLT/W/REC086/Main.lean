import AKLT.Blueprint.Rec.NodesRenewal

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC086

open AKLT.Blueprint.Rec

private lemma unweighted_row
    (m : PairType → PairType → ℕ → ℝ) (h : PairType → ℝ)
    (θ ρ : ℝ) (hθ : 0 < θ) (hθ1 : θ < 1)
    (hrows : RenewalRows m h θ ρ) (X : PairType) :
    Summable (fun j : PairType × ℕ => m X j.1 j.2 * h j.1) ∧
      (∑' j : PairType × ℕ, m X j.1 j.2 * h j.1) ≤ ρ * h X := by
  have hwt : ∀ j : PairType × ℕ, 1 ≤ θ ^ (-(j.2 : ℤ)) := by
    intro j
    rw [zpow_neg, zpow_natCast]
    apply (one_le_inv₀ (pow_pos hθ j.2)).2
    exact pow_le_one₀ hθ.le hθ1.le
  have hnonneg : ∀ j : PairType × ℕ, 0 ≤ m X j.1 j.2 * h j.1 := by
    intro j
    exact mul_nonneg (hrows.1 X j.1 j.2) (hrows.2.1 j.1).le
  have hle : ∀ j : PairType × ℕ,
      m X j.1 j.2 * h j.1 ≤
        m X j.1 j.2 * h j.1 * θ ^ (-(j.2 : ℤ)) := by
    intro j
    exact le_mul_of_one_le_right (hnonneg j) (hwt j)
  have hs := Summable.of_nonneg_of_le hnonneg hle (hrows.2.2.1 X)
  refine ⟨hs, ?_⟩
  calc
    (∑' j : PairType × ℕ, m X j.1 j.2 * h j.1) ≤
        ∑' j : PairType × ℕ, m X j.1 j.2 * h j.1 * θ ^ (-(j.2 : ℤ)) :=
      hs.tsum_le_tsum hle (hrows.2.2.1 X)
    _ ≤ ρ * h X := hrows.2.2.2 X

private lemma renewalOp_bound
    (m : PairType → PairType → ℕ → ℝ) (h : PairType → ℝ)
    (θ ρ C : ℝ) (hθ : 0 < θ) (hθ1 : θ < 1)
    (hrows : RenewalRows m h θ ρ) (hC : 0 ≤ C)
    (g : PairType → ℤ → ℝ)
    (hg : ∀ Y d, 0 ≤ g Y d ∧ g Y d ≤ C * h Y)
    (X : PairType) (d : ℤ) :
    Summable (fun j : PairType × ℕ => m X j.1 j.2 * g j.1 (d - j.2)) ∧
      renewalOp m g X d ≤ C * ρ * h X := by
  obtain ⟨hb, hrow⟩ := unweighted_row m h θ ρ hθ hθ1 hrows X
  have hupper : Summable (fun j : PairType × ℕ => C * (m X j.1 j.2 * h j.1)) :=
    hb.mul_left C
  have hpoint : ∀ j : PairType × ℕ,
      m X j.1 j.2 * g j.1 (d - j.2) ≤ C * (m X j.1 j.2 * h j.1) := by
    intro j
    calc
      m X j.1 j.2 * g j.1 (d - j.2) ≤ m X j.1 j.2 * (C * h j.1) :=
        mul_le_mul_of_nonneg_left (hg j.1 (d - j.2)).2 (hrows.1 X j.1 j.2)
      _ = C * (m X j.1 j.2 * h j.1) := by ring
  have htermnonneg : ∀ j : PairType × ℕ,
      0 ≤ m X j.1 j.2 * g j.1 (d - j.2) := by
    intro j
    exact mul_nonneg (hrows.1 X j.1 j.2) (hg j.1 (d - j.2)).1
  have hs := Summable.of_nonneg_of_le htermnonneg hpoint hupper
  constructor
  · exact hs
  · calc
      renewalOp m g X d ≤
          ∑' j : PairType × ℕ, C * (m X j.1 j.2 * h j.1) :=
        hs.tsum_le_tsum hpoint hupper
      _ = C * (∑' j : PairType × ℕ, m X j.1 j.2 * h j.1) :=
        hb.tsum_mul_left C
      _ ≤ C * (ρ * h X) := mul_le_mul_of_nonneg_left hrow hC
      _ = C * ρ * h X := by ring

theorem main : AKLT.Blueprint.Rec.RenewalRemainderStatement := by
  intro m h θ ρ hθ hθ1 hρ hρ1 hrows F hF k X d
  have hminpos : 0 < hmin h := lt_min (hrows.2.1 .B) (hrows.2.1 .C)
  have hminle : ∀ Y : PairType, hmin h ≤ h Y := by
    intro Y
    cases Y <;> simp [hmin]
  have hscale : 0 ≤ 2 / hmin h := by positivity
  have hbase : ∀ Y : PairType, ∀ e : ℤ,
      0 ≤ F Y e ∧ F Y e ≤ (2 / hmin h) * h Y := by
    intro Y e
    constructor
    · exact (hF Y e).1
    · calc
        F Y e ≤ 2 := (hF Y e).2
        _ = (2 / hmin h) * hmin h := by field_simp
        _ ≤ (2 / hmin h) * h Y := mul_le_mul_of_nonneg_left (hminle Y) hscale
  have hbound : ∀ n : ℕ, ∀ Y : PairType, ∀ e : ℤ,
      0 ≤ renewalIterate m F n Y e ∧
        renewalIterate m F n Y e ≤ (2 / hmin h) * ρ ^ n * h Y := by
    intro n
    induction n with
    | zero =>
        intro Y e
        constructor
        · exact (hbase Y e).1
        · simpa [renewalIterate] using (hbase Y e).2
    | succ n ih =>
        intro Y e
        have hC : 0 ≤ (2 / hmin h) * ρ ^ n := by positivity
        have hstep := renewalOp_bound m h θ ρ ((2 / hmin h) * ρ ^ n)
          hθ hθ1 hrows hC (renewalIterate m F n) (fun Z t => ih Z t) Y e
        constructor
        · apply tsum_nonneg
          intro j
          exact mul_nonneg (hrows.1 Y j.1 j.2) (ih j.1 (e - j.2)).1
        · simpa [renewalIterate, pow_succ, mul_assoc, mul_left_comm, mul_comm] using hstep.2
  exact (hbound k X d).2

end AKLT.W.REC086
