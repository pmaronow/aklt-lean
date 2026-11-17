module
public import AKLT.Blueprint.Gap.NodesFinite

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Gap
attribute [local instance] Classical.propDecidable

namespace AKLT.W.GAP007

private lemma hamming_le_outside_add_volume_indicator
    {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type}
    [∀ x, Fintype (S x)] (U : Finset ι) (σ τ : Config S) :
    (hamming σ τ : ℝ) ≤ ((Finset.univ \ U).card : ℝ) +
      (Fintype.card ι : ℝ) * (if AgreeOn U σ τ then 0 else 1) := by
  classical
  by_cases hagree : AgreeOn U σ τ
  · have hsubset : (Finset.univ.filter fun x => σ x ≠ τ x) ⊆ Finset.univ \ U := by
      intro x hx
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
      intro hxU
      exact (Finset.mem_filter.mp hx).2 (hagree x hxU)
    have hcard := Finset.card_le_card hsubset
    change (↑(Finset.univ.filter fun x => σ x ≠ τ x).card : ℝ) ≤ _
    simpa [hagree] using (Nat.cast_le.mpr hcard :
      ((Finset.univ.filter fun x => σ x ≠ τ x).card : ℝ) ≤
        ((Finset.univ \ U).card : ℝ))
  · have hsubset : (Finset.univ.filter fun x => σ x ≠ τ x) ⊆ Finset.univ :=
      Finset.filter_subset _ _
    have hcard := Finset.card_le_card hsubset
    change (↑(Finset.univ.filter fun x => σ x ≠ τ x).card : ℝ) ≤ _
    have hNat : (Finset.univ.filter fun x => σ x ≠ τ x).card ≤ Fintype.card ι := by
      simpa using hcard
    have hcast : ((Finset.univ.filter fun x => σ x ≠ τ x).card : ℝ) ≤
        (Fintype.card ι : ℝ) := Nat.cast_le.mpr hNat
    simp only [hagree, ite_false]
    have houtNonneg : (0 : ℝ) ≤ ((Finset.univ \ U).card : ℝ) := Nat.cast_nonneg _
    nlinarith [hcast, houtNonneg]

theorem main : AKLT.Blueprint.Gap.HammingLocalizationStatement := by
  classical
  unfold AKLT.Blueprint.Gap.HammingLocalizationStatement
  intro ι hι hιDec S hS p q hp hq c U
  let out : ℝ := (Finset.univ \ U).card
  let vol : ℝ := Fintype.card ι
  let indicator : Config S → Config S → ℝ := fun σ τ =>
    if AgreeOn U σ τ then 0 else 1
  have hpoint (σ τ : Config S) :
      (hamming σ τ : ℝ) ≤ out + vol * indicator σ τ := by
    simpa [out, vol, indicator] using
      hamming_le_outside_add_volume_indicator U σ τ
  have hsum :
      (∑ σ, ∑ τ, c.mass σ τ * (hamming σ τ : ℝ)) ≤
        ∑ σ, ∑ τ, c.mass σ τ * (out + vol * indicator σ τ) := by
    apply Finset.sum_le_sum
    intro σ _
    apply Finset.sum_le_sum
    intro τ _
    exact mul_le_mul_of_nonneg_left (hpoint σ τ) (c.nonnegative σ τ)
  have htotal : (∑ σ, ∑ τ, c.mass σ τ) = 1 := by
    calc
      (∑ σ, ∑ τ, c.mass σ τ) = ∑ σ, p σ := by
        apply Finset.sum_congr rfl
        intro σ _
        exact c.first_marginal σ
      _ = 1 := hp.2
  have hdis : (∑ σ, ∑ τ, c.mass σ τ * indicator σ τ) = disagreement c U := by
    unfold indicator disagreement
    apply Finset.sum_congr rfl
    intro σ _
    apply Finset.sum_congr rfl
    intro τ _
    by_cases hagree : AgreeOn U σ τ <;> simp [hagree]
  have hout : (∑ σ, ∑ τ, c.mass σ τ * out) = out := by
    calc
      (∑ σ, ∑ τ, c.mass σ τ * out) =
          (∑ σ, ∑ τ, c.mass σ τ) * out := by
        simp only [Finset.sum_mul]
      _ = out := by rw [htotal]; ring
  have hvol : (∑ σ, ∑ τ, c.mass σ τ * (vol * indicator σ τ)) =
      vol * disagreement c U := by
    calc
      (∑ σ, ∑ τ, c.mass σ τ * (vol * indicator σ τ)) =
          ∑ σ, ∑ τ, vol * (c.mass σ τ * indicator σ τ) := by
        apply Finset.sum_congr rfl
        intro σ _
        apply Finset.sum_congr rfl
        intro τ _
        ring
      _ = vol * (∑ σ, ∑ τ, c.mass σ τ * indicator σ τ) := by
        simp only [Finset.mul_sum]
      _ = vol * disagreement c U := by rw [hdis]
  have hright :
      (∑ σ, ∑ τ, c.mass σ τ * (out + vol * indicator σ τ)) =
        out + vol * disagreement c U := by
    calc
      _ = (∑ σ, ∑ τ, c.mass σ τ * out) +
          (∑ σ, ∑ τ, c.mass σ τ * (vol * indicator σ τ)) := by
        simp [mul_add, Finset.sum_add_distrib]
      _ = out + vol * disagreement c U := by rw [hout, hvol]
  simpa [couplingCost, out, vol] using hsum.trans_eq hright

end AKLT.W.GAP007

#print axioms AKLT.W.GAP007.main
