module
public import AKLT.Blueprint.Rec.NodesRenewal

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC087

open AKLT.Blueprint.Rec

private lemma source_bound
    (m : PairType → PairType → ℕ → ℝ) (h : PairType → ℝ)
    (q θ ρ CT : ℝ) (hq : 0 < q) (hqθ : q ^ 2 < θ)
    (hθ : 0 < θ) (hθ1 : θ < 1) (hCT : 0 ≤ CT) (hr : RenewalRows m h θ ρ) :
    ∀ X d, 0 ≤ renewalSource CT q X d ∧
      renewalSource CT q X d ≤ (max 2 CT / hmin h) * h X * θ ^ d := by
  have hmpos : 0 < hmin h := by
    unfold hmin
    exact lt_min (hr.2.1 .B) (hr.2.1 .C)
  have hmle (X : PairType) : hmin h ≤ h X := by
    cases X <;> simp [hmin]
  have hfactor (X : PairType) : max 2 CT ≤ (max 2 CT / hmin h) * h X := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hmpos).2
    exact mul_le_mul_of_nonneg_left (hmle X) (le_max_of_le_left (show 0 ≤ 2 by norm_num))
  intro X d
  by_cases hd : d ≤ 0
  · have hsource : renewalSource CT q X d = 2 := by
      simp [renewalSource, hd]
    have htheta : 1 ≤ θ ^ d := one_le_zpow_of_nonpos₀ hθ hθ1.le hd
    have htwo : 2 ≤ (max 2 CT / hmin h) * h X :=
      le_trans (le_max_left 2 CT) (hfactor X)
    constructor
    · rw [hsource]
      norm_num
    · rw [hsource]
      calc
        (2 : ℝ) ≤ (max 2 CT / hmin h) * h X := htwo
        _ = ((max 2 CT / hmin h) * h X) * 1 := by ring
        _ ≤ ((max 2 CT / hmin h) * h X) * θ ^ d :=
          mul_le_mul_of_nonneg_left htheta (le_of_lt (mul_pos (div_pos (by positivity) hmpos) (hr.2.1 X)))
  · have hdpos : 0 < d := lt_of_not_ge hd
    have hnat : (d.toNat : ℤ) = d := Int.toNat_of_nonneg (le_of_lt hdpos)
    have hpow : q ^ (2 * d.toNat) ≤ θ ^ d := by
      have hpowNat : (q ^ 2) ^ d.toNat ≤ θ ^ d.toNat :=
        pow_le_pow_left₀ (sq_nonneg q) hqθ.le _
      have hleft : q ^ (2 * d.toNat) = (q ^ 2) ^ d.toNat := by
        rw [← pow_mul]

      rw [hleft, ← hnat, zpow_natCast]
      exact hpowNat
    have hsource : renewalSource CT q X d = CT * q ^ (2 * d.toNat) := by
      simp [renewalSource, not_le.mpr hdpos]
    have hCTpow : CT * q ^ (2 * d.toNat) ≤ max 2 CT * θ ^ d := by
      calc
        CT * q ^ (2 * d.toNat) ≤ max 2 CT * q ^ (2 * d.toNat) :=
          mul_le_mul_of_nonneg_right (le_max_right 2 CT) (pow_nonneg hq.le _)
        _ ≤ max 2 CT * θ ^ d :=
          mul_le_mul_of_nonneg_left hpow (le_max_of_le_left (show 0 ≤ 2 by norm_num))
    constructor
    · rw [hsource]
      exact mul_nonneg hCT (pow_nonneg hq.le _)
    · rw [hsource]
      exact hCTpow.trans (mul_le_mul_of_nonneg_right (hfactor X) (zpow_nonneg hθ.le d))

private lemma iterate_bound
    (m : PairType → PairType → ℕ → ℝ) (h : PairType → ℝ)
    (θ ρ A : ℝ) (hθ : 0 < θ) (hρ : 0 ≤ ρ) (hA : 0 ≤ A)
    (hr : RenewalRows m h θ ρ) (g : PairType → ℤ → ℝ)
    (hsource : ∀ X d, 0 ≤ g X d ∧ g X d ≤ A * h X * θ ^ d) :
    ∀ k X d, 0 ≤ renewalIterate m g k X d ∧
      renewalIterate m g k X d ≤ A * ρ ^ k * h X * θ ^ d := by
  intro k
  induction k with
  | zero =>
      intro X d
      simpa [renewalIterate] using hsource X d
  | succ k ih =>
      intro X d
      let C : ℝ := A * ρ ^ k * θ ^ d
      have hC : 0 ≤ C := by
        dsimp [C]
        exact mul_nonneg (mul_nonneg hA (pow_nonneg hρ _)) (zpow_nonneg hθ.le _)
      have hrow : Summable (fun j : PairType × ℕ =>
          m X j.1 j.2 * h j.1 * θ ^ (-(j.2 : ℤ))) := hr.2.2.1 X
      have hpoint : ∀ j : PairType × ℕ,
          m X j.1 j.2 * renewalIterate m g k j.1 (d - (j.2 : ℤ)) ≤
            C * (m X j.1 j.2 * h j.1 * θ ^ (-(j.2 : ℤ))) := by
        intro j
        have hi := ih j.1 (d - (j.2 : ℤ))
        calc
          m X j.1 j.2 * renewalIterate m g k j.1 (d - (j.2 : ℤ)) ≤
              m X j.1 j.2 * (A * ρ ^ k * h j.1 * θ ^ (d - (j.2 : ℤ))) :=
            mul_le_mul_of_nonneg_left hi.2 (hr.1 X j.1 j.2)
          _ = C * (m X j.1 j.2 * h j.1 * θ ^ (-(j.2 : ℤ))) := by
            dsimp [C]
            rw [zpow_sub₀ hθ.ne', div_eq_mul_inv, zpow_neg]
            ring
      have hterm_nonneg : ∀ j : PairType × ℕ,
          0 ≤ m X j.1 j.2 * renewalIterate m g k j.1 (d - (j.2 : ℤ)) := by
        intro j
        exact mul_nonneg (hr.1 X j.1 j.2) (ih j.1 (d - (j.2 : ℤ))).1
      have hscaled : Summable (fun j : PairType × ℕ =>
          C * (m X j.1 j.2 * h j.1 * θ ^ (-(j.2 : ℤ)))) := hrow.mul_left C
      have hterms : Summable (fun j : PairType × ℕ =>
          m X j.1 j.2 * renewalIterate m g k j.1 (d - (j.2 : ℤ))) :=
        Summable.of_nonneg_of_le hterm_nonneg hpoint hscaled
      have hsum := Summable.tsum_le_tsum hpoint hterms hscaled
      rw [tsum_mul_left] at hsum
      have hupper : (∑' j : PairType × ℕ,
          m X j.1 j.2 * renewalIterate m g k j.1 (d - (j.2 : ℤ))) ≤
          C * (ρ * h X) := by
        calc
          _ ≤ C * (∑' j : PairType × ℕ,
              m X j.1 j.2 * h j.1 * θ ^ (-(j.2 : ℤ))) := hsum
          _ ≤ C * (ρ * h X) := mul_le_mul_of_nonneg_left (hr.2.2.2 X) hC
      constructor
      · apply tsum_nonneg
        exact hterm_nonneg
      · change (∑' j : PairType × ℕ,
          m X j.1 j.2 * renewalIterate m g k j.1 (d - (j.2 : ℤ))) ≤
          A * ρ ^ (k + 1) * h X * θ ^ d
        calc
          _ ≤ C * (ρ * h X) := hupper
          _ = A * ρ ^ (k + 1) * h X * θ ^ d := by
            dsimp [C]
            rw [pow_succ]
            ring

/-- The source iterate is controlled by the shifted weighted row bound. -/
theorem main : AKLT.Blueprint.Rec.RenewalSourceStatement := by
  intro m h q θ ρ CT hq hqθ hθ1 hρ hρ1 hCT hr k X d
  have hθ : 0 < θ := lt_trans (sq_pos_of_pos hq) hqθ
  have hmpos : 0 < hmin h := by
    unfold hmin
    exact lt_min (hr.2.1 .B) (hr.2.1 .C)
  let A : ℝ := max 2 CT / hmin h
  have hA : 0 ≤ A := by
    dsimp [A]
    exact div_nonneg (le_max_of_le_left (by norm_num)) hmpos.le
  have hsrc := source_bound m h q θ ρ CT hq hqθ hθ hθ1 hCT hr
  have hsrc' : ∀ Y z, 0 ≤ renewalSource CT q Y z ∧
      renewalSource CT q Y z ≤ A * h Y * θ ^ z := by
    intro Y z
    have hs := hsrc Y z
    constructor
    · exact hs.1
    · simpa [A, renewalSource] using hs.2
  have hbound := iterate_bound m h θ ρ A hθ hρ.le hA hr (renewalSource CT q) hsrc'
  exact hbound k X d |>.2

end AKLT.W.REC087
