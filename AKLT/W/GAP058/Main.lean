module
public import AKLT.Blueprint.Gap.NodesShell

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Gap

namespace AKLT.W.GAP058

private theorem hamming_localization
    {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type} [∀ x, Fintype (S x)]
    {p q : Weight (Config S)} (hp : Probability p) (c : Coupling p q)
    (U : Finset ι) :
    couplingCost c ≤ ((Finset.univ \ U).card : ℝ) +
      (Fintype.card ι : ℝ) * disagreement c U := by
  classical
  have hpoint (σ τ : Config S) :
      (hamming σ τ : ℝ) ≤ ((Finset.univ \ U).card : ℝ) +
        (Fintype.card ι : ℝ) * (if AgreeOn U σ τ then 0 else 1) := by
    by_cases hagree : AgreeOn U σ τ
    · have hsub : (Finset.univ.filter fun x => σ x ≠ τ x) ⊆ Finset.univ \ U := by
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
        intro hxU
        exact hx (hagree x hxU)
      have hcard := Finset.card_le_card hsub
      have hreal : (hamming σ τ : ℝ) ≤ ((Finset.univ \ U).card : ℝ) := by
        exact_mod_cast hcard
      simpa [hagree] using hreal
    · have hcard : hamming σ τ ≤ Fintype.card ι := by
        calc
          hamming σ τ = (Finset.univ.filter fun x => σ x ≠ τ x).card := rfl
          _ ≤ Finset.univ.card := Finset.card_filter_le _ _
          _ = Fintype.card ι := Finset.card_univ
      have hreal : (hamming σ τ : ℝ) ≤ (Fintype.card ι : ℝ) := by
        exact_mod_cast hcard
      have hle : (Fintype.card ι : ℝ) ≤ ((Finset.univ \ U).card : ℝ) + Fintype.card ι := by
        have hcard0 : (0 : ℝ) ≤ (Fintype.card ι : ℝ) := by positivity
        have hcomp0 : (0 : ℝ) ≤ ((Finset.univ \ U).card : ℝ) := by positivity
        linarith
      simpa [hagree] using hreal.trans hle
  have htotal : (∑ σ, ∑ τ, c.mass σ τ) = 1 := by
    calc
      (∑ σ, ∑ τ, c.mass σ τ) = ∑ σ, p σ := by
        apply Finset.sum_congr rfl
        intro σ _
        exact c.first_marginal σ
      _ = 1 := hp.2
  have hdis :
      (∑ σ, ∑ τ, c.mass σ τ * (if AgreeOn U σ τ then 0 else 1)) = disagreement c U := by
    simp [disagreement, mul_ite]
  have hsumConst :
      (∑ σ, ∑ τ, c.mass σ τ * ((Finset.univ \ U).card : ℝ)) =
        ((Finset.univ \ U).card : ℝ) := by
    calc
      (∑ σ, ∑ τ, c.mass σ τ * ((Finset.univ \ U).card : ℝ)) =
          (∑ σ, ∑ τ, c.mass σ τ) * ((Finset.univ \ U).card : ℝ) := by
        simp_rw [Finset.sum_mul]
      _ = ((Finset.univ \ U).card : ℝ) := by rw [htotal]; ring
  have hsumDis :
      (∑ σ, ∑ τ, c.mass σ τ *
        ((Fintype.card ι : ℝ) * (if AgreeOn U σ τ then 0 else 1))) =
          (Fintype.card ι : ℝ) * disagreement c U := by
    calc
      (∑ σ, ∑ τ, c.mass σ τ *
          ((Fintype.card ι : ℝ) * (if AgreeOn U σ τ then 0 else 1))) =
        ∑ σ, ∑ τ, (Fintype.card ι : ℝ) *
          (c.mass σ τ * (if AgreeOn U σ τ then 0 else 1)) := by
        apply Finset.sum_congr rfl
        intro σ _
        apply Finset.sum_congr rfl
        intro τ _
        ring
      _ = (Fintype.card ι : ℝ) *
          (∑ σ, ∑ τ, c.mass σ τ * (if AgreeOn U σ τ then 0 else 1)) := by
        simp_rw [Finset.mul_sum]
      _ = (Fintype.card ι : ℝ) * disagreement c U := by rw [hdis]
  calc
    couplingCost c = ∑ σ, ∑ τ, c.mass σ τ * (hamming σ τ : ℝ) := rfl
    _ ≤ ∑ σ, ∑ τ, c.mass σ τ *
          (((Finset.univ \ U).card : ℝ) +
            (Fintype.card ι : ℝ) * (if AgreeOn U σ τ then 0 else 1)) := by
      apply Finset.sum_le_sum
      intro σ _
      apply Finset.sum_le_sum
      intro τ _
      exact mul_le_mul_of_nonneg_left (hpoint σ τ) (c.nonnegative σ τ)
    _ = ((Finset.univ \ U).card : ℝ) +
          (Fintype.card ι : ℝ) * disagreement c U := by
      simp_rw [mul_add]
      simp only [Finset.sum_add_distrib]
      rw [hsumConst, hsumDis]

/-- Convert the stopped disagreement estimate to a Hamming-cost bound, retaining its coupling. -/
theorem main : AKLT.Blueprint.Gap.StoppedHammingConversionStatement := by
  intro P l p Mstar α n d hd hdq hqle hthreshold hn hspacing hradius hstopped hcounts hprob
    a y hy η ξ hηξ
  have hnNat : 4 ≤ n := hn
  have hrealn : (n : ℝ) ≤ shellSpacing (n ^ 8) := hspacing
  have hu : max Mstar (geometryThreshold l) ≤ n ^ 8 := hthreshold
  obtain ⟨c, hc⟩ := hstopped a (n ^ 8) hu y hy η ξ hηξ n hnNat hrealn
  have hU : farSites a y (n ^ 8) ((n : ℝ) * shellSpacing (n ^ 8)) =
      farSites a y (n ^ 8) ((n : ℝ) ^ 3) := by
    rw [hradius]
  rw [hU] at hc
  let U := farSites a y (n ^ 8) ((n : ℝ) ^ 3)
  have hlocal := hamming_localization (hprob a η) c U
  have hdisBound : disagreement c U ≤ (1 - d) ^ (n - 3) := by
    have hq0 : 0 ≤ p * α ^ (16 * l) := by linarith
    have hdle1 : d ≤ 1 := le_trans hdq hqle
    have hbases : 0 ≤ 1 - p * α ^ (16 * l) ∧
        1 - p * α ^ (16 * l) ≤ 1 - d := by
      constructor <;> linarith
    have hpown : (1 - p * α ^ (16 * l)) ^ (n - 3) ≤ (1 - d) ^ (n - 3) :=
      pow_le_pow_left₀ hbases.1 hbases.2 (n - 3)
    exact hc.trans hpown
  have hcount := hcounts a y
  have hvol : (Fintype.card (square a (n ^ 8)) : ℝ) ≤ 25 * (n : ℝ) ^ 16 := hcount.2
  have hcomp : ((Finset.univ \ U).card : ℝ) ≤ 25 * (n : ℝ) ^ 6 := by
    simpa [U, hradius] using hcount.1
  have hprod : (Fintype.card (square a (n ^ 8)) : ℝ) * disagreement c U ≤
      25 * (n : ℝ) ^ 16 * (1 - d) ^ (n - 3) := by
    calc
      (Fintype.card (square a (n ^ 8)) : ℝ) * disagreement c U ≤
          (Fintype.card (square a (n ^ 8)) : ℝ) * (1 - d) ^ (n - 3) :=
        mul_le_mul_of_nonneg_left hdisBound (by positivity)
      _ ≤ 25 * (n : ℝ) ^ 16 * (1 - d) ^ (n - 3) :=
        mul_le_mul_of_nonneg_right hvol (by
          apply pow_nonneg
          linarith)
  refine ⟨c, ?_⟩
  calc
    couplingCost c ≤ ((Finset.univ \ U).card : ℝ) +
        (Fintype.card (square a (n ^ 8)) : ℝ) * disagreement c U := hlocal
    _ ≤ 25 * (n : ℝ) ^ 6 +
        25 * (n : ℝ) ^ 16 * (1 - d) ^ (n - 3) := add_le_add hcomp hprod

end AKLT.W.GAP058
