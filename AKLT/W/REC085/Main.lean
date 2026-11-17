import AKLT.Blueprint.Rec.NodesRenewal

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Rec

namespace AKLT.W.REC085

private def weightedRow (m : PairType → PairType → ℕ → ℝ)
    (h : PairType → ℝ) (θ : ℝ) (X : PairType) (j : PairType × ℕ) : ℝ :=
  m X j.1 j.2 * h j.1 * θ ^ (-(j.2 : ℤ))

private def BoundedPos (f : PairType → ℤ → ℝ) : Prop :=
  ∃ B : ℝ, 0 ≤ B ∧ ∀ X d, 0 ≤ f X d ∧ f X d ≤ B

private theorem hmin_pos {m : PairType → PairType → ℕ → ℝ} {θ ρ : ℝ}
    (h : PairType → ℝ) (hrows : RenewalRows m h θ ρ) :
    0 < hmin h := by
  exact lt_min (hrows.2.1 .B) (hrows.2.1 .C)

private theorem hmin_le (h : PairType → ℝ) (Y : PairType) : hmin h ≤ h Y := by
  cases Y <;> simp [hmin]

private theorem h_le_hmax (h : PairType → ℝ) (X : PairType) : h X ≤ hmax h := by
  cases X <;> simp [hmax]

private theorem theta_weight_ge_one {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (s : ℕ) :
    1 ≤ θ ^ (-(s : ℤ)) := by
  rw [zpow_neg, zpow_natCast]
  apply (one_le_inv₀ (pow_pos hθ s)).2
  exact pow_le_one₀ (le_of_lt hθ) hθ1.le

private theorem op_term_le_weighted
    {m : PairType → PairType → ℕ → ℝ} {h : PairType → ℝ} {θ ρ : ℝ}
    (hθ : 0 < θ) (hθ1 : θ < 1) (hrows : RenewalRows m h θ ρ)
    {f : PairType → ℤ → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ X d, 0 ≤ f X d ∧ f X d ≤ B)
    (X : PairType) (d : ℤ) (j : PairType × ℕ) :
    0 ≤ m X j.1 j.2 * f j.1 (d - (j.2 : ℤ)) ∧
      m X j.1 j.2 * f j.1 (d - (j.2 : ℤ)) ≤
        (B / hmin h) * weightedRow m h θ X j := by
  have hm := hrows.1 X j.1 j.2
  have hh := hmin_le h j.1
  have ht := theta_weight_ge_one hθ hθ1 j.2
  have hp : hmin h ≤ h j.1 * θ ^ (-(j.2 : ℤ)) := by
    calc
      hmin h ≤ h j.1 := hh
      _ ≤ h j.1 * θ ^ (-(j.2 : ℤ)) := by
        exact le_mul_of_one_le_right (hrows.2.1 j.1).le ht
  have hscale : B ≤ (B / hmin h) * (h j.1 * θ ^ (-(j.2 : ℤ))) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (hmin_pos h hrows)).2
    exact mul_le_mul_of_nonneg_left hp hB
  constructor
  · exact mul_nonneg hm (hf j.1 (d - (j.2 : ℤ))).1
  · calc
      m X j.1 j.2 * f j.1 (d - (j.2 : ℤ)) ≤ m X j.1 j.2 * B :=
        mul_le_mul_of_nonneg_left (hf j.1 (d - (j.2 : ℤ))).2 hm
      _ ≤ m X j.1 j.2 * ((B / hmin h) * (h j.1 * θ ^ (-(j.2 : ℤ)))) :=
        mul_le_mul_of_nonneg_left hscale hm
      _ = (B / hmin h) * weightedRow m h θ X j := by
        dsimp [weightedRow]
        ring

private theorem op_summable
    {m : PairType → PairType → ℕ → ℝ} {h : PairType → ℝ} {θ ρ : ℝ}
    (hθ : 0 < θ) (hθ1 : θ < 1) (hrows : RenewalRows m h θ ρ)
    {f : PairType → ℤ → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ X d, 0 ≤ f X d ∧ f X d ≤ B) (X : PairType) (d : ℤ) :
    Summable (fun j : PairType × ℕ => m X j.1 j.2 * f j.1 (d - (j.2 : ℤ))) := by
  apply Summable.of_nonneg_of_le (fun j => (op_term_le_weighted hθ hθ1 hrows hB hf X d j).1)
  · intro j
    exact (op_term_le_weighted hθ hθ1 hrows hB hf X d j).2
  · exact Summable.mul_left (B / hmin h) (hrows.2.2.1 X)

private theorem op_nonneg
    {m : PairType → PairType → ℕ → ℝ} {h : PairType → ℝ} {θ ρ : ℝ}
    (hθ : 0 < θ) (hθ1 : θ < 1) (hrows : RenewalRows m h θ ρ)
    {f : PairType → ℤ → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ X d, 0 ≤ f X d ∧ f X d ≤ B) (X : PairType) (d : ℤ) :
    0 ≤ renewalOp m f X d := by
  unfold renewalOp
  have _hs := op_summable hθ hθ1 hrows hB hf X d
  exact tsum_nonneg (fun j =>
    mul_nonneg (hrows.1 X j.1 j.2) (hf j.1 (d - (j.2 : ℤ))).1)

private theorem op_add
    {m : PairType → PairType → ℕ → ℝ} {h : PairType → ℝ} {θ ρ : ℝ}
    (hθ : 0 < θ) (hθ1 : θ < 1) (hrows : RenewalRows m h θ ρ)
    {f g : PairType → ℤ → ℝ} {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hf : ∀ X d, 0 ≤ f X d ∧ f X d ≤ B)
    (hg : ∀ X d, 0 ≤ g X d ∧ g X d ≤ C) (X : PairType) (d : ℤ) :
    renewalOp m (fun Y e => f Y e + g Y e) X d =
      renewalOp m f X d + renewalOp m g X d := by
  unfold renewalOp
  have hsumf := op_summable hθ hθ1 hrows hB hf X d
  have hsumg := op_summable hθ hθ1 hrows hC hg X d
  calc
    (∑' j : PairType × ℕ, m X j.1 j.2 * (f j.1 (d - (j.2 : ℤ)) + g j.1 (d - (j.2 : ℤ)))) =
      ∑' j : PairType × ℕ,
        (m X j.1 j.2 * f j.1 (d - (j.2 : ℤ)) +
          m X j.1 j.2 * g j.1 (d - (j.2 : ℤ))) := by
            congr 1
            funext j
            ring
    _ = _ := hsumf.tsum_add hsumg

private theorem op_mono
    {m : PairType → PairType → ℕ → ℝ} {h : PairType → ℝ} {θ ρ : ℝ}
    (hθ : 0 < θ) (hθ1 : θ < 1) (hrows : RenewalRows m h θ ρ)
    {f g : PairType → ℤ → ℝ} {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hf : ∀ X d, 0 ≤ f X d ∧ f X d ≤ B)
    (hg : ∀ X d, 0 ≤ g X d ∧ g X d ≤ C)
    (hle : ∀ X d, f X d ≤ g X d) (X : PairType) (d : ℤ) :
    renewalOp m f X d ≤ renewalOp m g X d := by
  have hsf := op_summable hθ hθ1 hrows hB hf X d
  have hsg := op_summable hθ hθ1 hrows hC hg X d
  exact Summable.tsum_le_tsum
    (fun j => mul_le_mul_of_nonneg_left (hle j.1 (d - (j.2 : ℤ))) (hrows.1 X j.1 j.2))
    hsf hsg


private theorem op_le_bound
    {m : PairType → PairType → ℕ → ℝ} {h : PairType → ℝ} {θ ρ : ℝ}
    (hθ : 0 < θ) (hθ1 : θ < 1) (hρ : 0 < ρ) (hrows : RenewalRows m h θ ρ)
    {f : PairType → ℤ → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ X d, 0 ≤ f X d ∧ f X d ≤ B) (X : PairType) (d : ℤ) :
    renewalOp m f X d ≤ B * (ρ * hmax h / hmin h) := by
  have hsum := op_summable hθ hθ1 hrows hB hf X d
  have hcoef := hrows.2.2.1 X
  have hrow := hrows.2.2.2 X
  have hC : 0 ≤ B / hmin h := div_nonneg hB (le_of_lt (hmin_pos h hrows))
  have htsum := Summable.tsum_le_tsum
    (fun j => (op_term_le_weighted hθ hθ1 hrows hB hf X d j).2)
    hsum (Summable.mul_left (B / hmin h) hcoef)
  rw [tsum_mul_left] at htsum
  calc
    renewalOp m f X d ≤ (B / hmin h) * (∑' j : PairType × ℕ, weightedRow m h θ X j) := by
      exact htsum
    _ ≤ (B / hmin h) * (ρ * h X) := mul_le_mul_of_nonneg_left hrow hC
    _ ≤ (B / hmin h) * (ρ * hmax h) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (h_le_hmax h X) hρ.le) hC
    _ = B * (ρ * hmax h / hmin h) := by
      unfold hmin hmax
      field_simp [ne_of_gt (hmin_pos h hrows)]

private theorem hmax_pos {m : PairType → PairType → ℕ → ℝ} {θ ρ : ℝ}
    (h : PairType → ℝ) (hrows : RenewalRows m h θ ρ) :
    0 < hmax h := by
  change 0 < max (h .B) (h .C)
  exact lt_of_lt_of_le (hrows.2.1 .B) (le_max_left _ _)

private theorem renewalOp_bounded
    {m : PairType → PairType → ℕ → ℝ} {h : PairType → ℝ} {θ ρ : ℝ}
    (hθ : 0 < θ) (hθ1 : θ < 1) (hρ : 0 < ρ) (hrows : RenewalRows m h θ ρ)
    {f : PairType → ℤ → ℝ} (hf : BoundedPos f) :
    BoundedPos (renewalOp m f) := by
  rcases hf with ⟨B, hB, hf⟩
  refine ⟨B * (ρ * hmax h / hmin h), ?_, ?_⟩
  · have hhmax := hmax_pos h hrows
    have hhmin := hmin_pos h hrows
    positivity
  · intro X d
    exact ⟨op_nonneg hθ hθ1 hrows hB hf X d,
      op_le_bound hθ hθ1 hρ hrows hB hf X d⟩

private theorem boundedPos_add {f g : PairType → ℤ → ℝ}
    (hf : BoundedPos f) (hg : BoundedPos g) : BoundedPos (fun X d => f X d + g X d) := by
  rcases hf with ⟨B, hB, hf⟩
  rcases hg with ⟨C, hC, hg⟩
  refine ⟨B + C, add_nonneg hB hC, ?_⟩
  intro X d
  exact ⟨add_nonneg (hf X d).1 (hg X d).1, add_le_add (hf X d).2 (hg X d).2⟩

private theorem boundedPos_sum_range {g : ℕ → PairType → ℤ → ℝ}
    (hg : ∀ j, BoundedPos (g j)) (k : ℕ) :
    BoundedPos (fun X d => ∑ j ∈ Finset.range k, g j X d) := by
  induction k with
  | zero =>
      refine ⟨0, le_rfl, ?_⟩
      intro X d
      simp
  | succ k ih =>
      rcases ih with ⟨B, hB, hf⟩
      rcases hg k with ⟨C, hC, hc⟩
      refine ⟨B + C, add_nonneg hB hC, ?_⟩
      intro X d
      change 0 ≤ (∑ j ∈ Finset.range (k + 1), g j X d) ∧
        (∑ j ∈ Finset.range (k + 1), g j X d) ≤ B + C
      rw [Finset.sum_range_succ]
      exact ⟨add_nonneg (hf X d).1 (hc X d).1, add_le_add (hf X d).2 (hc X d).2⟩

private theorem op_sum_range
    {m : PairType → PairType → ℕ → ℝ} {h : PairType → ℝ} {θ ρ : ℝ}
    (hθ : 0 < θ) (hθ1 : θ < 1) (hrows : RenewalRows m h θ ρ)
    {g : ℕ → PairType → ℤ → ℝ} (hg : ∀ j, BoundedPos (g j))
    (k : ℕ) (X : PairType) (d : ℤ) :
    renewalOp m (fun Y e => ∑ j ∈ Finset.range k, g j Y e) X d =
      ∑ j ∈ Finset.range k, renewalOp m (g j) X d := by
  induction k with
  | zero => simp [renewalOp]
  | succ k ih =>
      rcases boundedPos_sum_range hg k with ⟨B, hB, hb⟩
      rcases hg k with ⟨C, hC, hc⟩
      have hfun : (fun Y e => ∑ j ∈ Finset.range (k + 1), g j Y e) =
          (fun Y e => (∑ j ∈ Finset.range k, g j Y e) + g k Y e) := by
        funext Y e
        simp [Finset.sum_range_succ]
      rw [hfun]
      rw [op_add hθ hθ1 hrows hB hC hb hc X d]
      rw [ih]
      simp [Finset.sum_range_succ]

private theorem iterate_bounded
    {m : PairType → PairType → ℕ → ℝ} {h : PairType → ℝ} {θ ρ : ℝ}
    (hθ : 0 < θ) (hθ1 : θ < 1) (hρ : 0 < ρ) (hrows : RenewalRows m h θ ρ)
    {f : PairType → ℤ → ℝ} (hf : BoundedPos f) :
    ∀ k, BoundedPos (renewalIterate m f k) := by
  intro k
  induction k with
  | zero => simpa [renewalIterate] using hf
  | succ k ih =>
      simpa [renewalIterate] using renewalOp_bounded hθ hθ1 hρ hrows ih

private theorem renewalSource_bounded {q θ CT : ℝ} (hq : 0 < q)
    (hqθ : q ^ 2 < θ) (hθ1 : θ < 1) (hCT : 0 ≤ CT) :
    BoundedPos (renewalSource CT q) := by
  refine ⟨max 2 CT, (show (0 : ℝ) ≤ 2 by norm_num).trans (le_max_left _ _), ?_⟩
  intro X d
  by_cases hd : d ≤ 0
  · simp [renewalSource, hd]
  · have hdpos : 0 < d := by omega
    have hqle : q ≤ 1 := by
      have hq2 : q ^ 2 < 1 := lt_trans hqθ hθ1
      nlinarith
    have hpow : q ^ (2 * d.toNat) ≤ 1 := pow_le_one₀ hq.le hqle
    have hsource : 0 ≤ CT * q ^ (2 * d.toNat) := mul_nonneg hCT (by positivity)
    have hmul : CT * q ^ (2 * d.toNat) ≤ CT := by
      simpa using mul_le_mul_of_nonneg_left hpow hCT
    have hsource_le : CT * q ^ (2 * d.toNat) ≤ max 2 CT :=
      hmul.trans (le_max_right _ _)
    unfold renewalSource
    by_cases hdepth : d ≤ 0
    · exact False.elim (hd hdepth)
    · simpa [hdepth] using And.intro hsource hsource_le

private theorem range_sum_succ_shift (f : ℕ → ℝ) (k : ℕ) :
    (∑ j ∈ Finset.range k, f (j + 1)) + f 0 =
      ∑ j ∈ Finset.range (k + 1), f j := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        (∑ j ∈ Finset.range (k + 1), f (j + 1)) + f 0 =
            ((∑ j ∈ Finset.range k, f (j + 1)) + f (k + 1)) + f 0 := by
              rw [Finset.sum_range_succ]
        _ = ((∑ j ∈ Finset.range k, f (j + 1)) + f 0) + f (k + 1) := by ring
        _ = (∑ j ∈ Finset.range (k + 1), f j) + f (k + 1) := by rw [ih]
        _ = ∑ j ∈ Finset.range (k + 1 + 1), f j :=
              (Finset.sum_range_succ f (k + 1)).symm

/-- Finite positive iteration of the renewal inequality, with the integer-depth
extension handled by the global bound on F. -/
theorem main : AKLT.Blueprint.Rec.RenewalFiniteIterationStatement := by
  intro m h q θ ρ CT hq hqθ hθ1 hρ hρ1 hCT hrows F hF hrec k
  have hθ : 0 < θ := lt_of_le_of_lt (sq_nonneg q) hqθ
  have hFB : BoundedPos F := ⟨2, by norm_num, hF⟩
  have hsource := renewalSource_bounded hq hqθ hθ1 hCT
  have hrecZ : ∀ X d, F X d ≤ renewalOp m F X d + renewalSource CT q X d := by
    intro X d
    by_cases hd : d ≤ 0
    · have hop := op_nonneg hθ hθ1 hrows (by norm_num) hF X d
      have htwo : F X d ≤ 2 := (hF X d).2
      simpa [renewalSource, hd] using (show F X d ≤ renewalOp m F X d + 2 by linarith)
    · have hdpos : 0 < d := by omega
      have hnat : 1 ≤ d.toNat := by omega
      have hcast : (d.toNat : ℤ) = d := Int.toNat_of_nonneg (le_of_lt hdpos)
      have hr := hrec X d.toNat hnat
      simpa [renewalSource, hd, hcast] using hr
  have hshiftSum (k : ℕ) (X : PairType) (d : ℤ) :
      (∑ j ∈ Finset.range k, renewalIterate m (renewalSource CT q) (j + 1) X d) +
        renewalSource CT q X d =
          ∑ j ∈ Finset.range (k + 1), renewalIterate m (renewalSource CT q) j X d := by
    simpa [renewalIterate] using
      range_sum_succ_shift (fun j => renewalIterate m (renewalSource CT q) j X d) k
  induction k with
  | zero =>
      intro X d
      simp [renewalIterate]
  | succ k ih =>
      intro X d
      let g : ℕ → PairType → ℤ → ℝ := fun j => renewalIterate m (renewalSource CT q) j
      let U : PairType → ℤ → ℝ := fun Y e => ∑ j ∈ Finset.range k, g j Y e
      let R : PairType → ℤ → ℝ := fun Y e => renewalIterate m F k Y e + U Y e
      have hg : ∀ j, BoundedPos (g j) := by
        intro j
        exact iterate_bounded hθ hθ1 hρ hrows hsource j
      have hU : BoundedPos U := by
        exact boundedPos_sum_range hg k
      have hIterF : BoundedPos (renewalIterate m F k) :=
        iterate_bounded hθ hθ1 hρ hrows hFB k
      have hR : BoundedPos R := by
        simpa [R, U] using boundedPos_add hIterF hU
      have hmono : renewalOp m F X d ≤ renewalOp m R X d := by
        apply op_mono hθ hθ1 hrows hFB.choose_spec.1 hR.choose_spec.1
          hFB.choose_spec.2 hR.choose_spec.2
        intro Y e
        have := ih Y e
        simpa [R, U, g] using this
      have hdecomp : renewalOp m R X d =
          renewalIterate m F (k + 1) X d +
            ∑ j ∈ Finset.range k, renewalIterate m (renewalSource CT q) (j + 1) X d := by
        calc
          renewalOp m R X d =
              renewalOp m (renewalIterate m F k) X d + renewalOp m U X d := by
                exact op_add hθ hθ1 hrows hIterF.choose_spec.1 hU.choose_spec.1
                  hIterF.choose_spec.2 hU.choose_spec.2 X d
          _ = renewalIterate m F (k + 1) X d +
                ∑ j ∈ Finset.range k, renewalOp m (g j) X d := by
                  rw [op_sum_range hθ hθ1 hrows hg k X d]
                  rfl
          _ = renewalIterate m F (k + 1) X d +
                ∑ j ∈ Finset.range k, renewalIterate m (renewalSource CT q) (j + 1) X d := by
                  simp [g, renewalIterate]
      calc
        F X d ≤ renewalOp m F X d + renewalSource CT q X d := hrecZ X d
        _ ≤ renewalOp m R X d + renewalSource CT q X d := add_le_add hmono le_rfl
        _ = renewalIterate m F (k + 1) X d +
              ∑ j ∈ Finset.range k, renewalIterate m (renewalSource CT q) (j + 1) X d +
              renewalSource CT q X d := by rw [hdecomp]
        _ = renewalIterate m F (k + 1) X d +
              ∑ j ∈ Finset.range (k + 1), renewalIterate m (renewalSource CT q) j X d := by
                rw [← hshiftSum k X d]
                ring

end AKLT.W.REC085

#print axioms AKLT.W.REC085.main
