module
public import AKLT.W.REC016.Moments

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC016

theorem signed_power_nonneg {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    0 ≤ t^n + (-t)^n := by
  rw [neg_pow]
  rcases neg_one_pow_eq_or ℝ n with h | h <;> rw [h]
  · positivity
  · simp

theorem site_monomial_nonneg (s : Status) (m : Fin 3 → ℕ) :
    0 ≤ siteFunctional s (fun v => ∏ i, v i ^ m i) := by
  have hpos : 0 ≤ goldenRatio / icoRadius := by
    exact div_nonneg (by unfold goldenRatio; positivity) radius_pos.le
  have h1 := signed_power_nonneg (le_of_lt (inv_pos.mpr radius_pos))
  have hphi := signed_power_nonneg hpos
  have h10 := h1 (m 0)
  have h11 := h1 (m 1)
  have h12 := h1 (m 2)
  have hp0 := hphi (m 0)
  have hp1 := hphi (m 1)
  have hp2 := hphi (m 2)
  have hU : siteFunctional .U (fun v => ∏ i, v i ^ m i) =
      (1 / 12) * (
        0 ^ m 0 * ((icoRadius⁻¹)^m 1 + (-(icoRadius⁻¹))^m 1) *
          ((goldenRatio / icoRadius)^m 2 + (-(goldenRatio / icoRadius))^m 2) +
        0 ^ m 2 * ((icoRadius⁻¹)^m 0 + (-(icoRadius⁻¹))^m 0) *
          ((goldenRatio / icoRadius)^m 1 + (-(goldenRatio / icoRadius))^m 1) +
        0 ^ m 1 * ((icoRadius⁻¹)^m 2 + (-(icoRadius⁻¹))^m 2) *
          ((goldenRatio / icoRadius)^m 0 + (-(goldenRatio / icoRadius))^m 0)) := by
    simp [siteFunctional, Fintype.sum_option, spinWeight, spinVector,
      Fintype.sum_prod_type, Fin.sum_univ_three, Fin.prod_univ_three, Fin.sum_univ_two, icoVector,
      signValue, neg_div]
    ring
  cases s
  · rw [hU]
    have h00 : (0 : ℝ) ≤ 0 ^ m 0 := pow_nonneg (by norm_num) _
    have h01 : (0 : ℝ) ≤ 0 ^ m 1 := pow_nonneg (by norm_num) _
    have h02 : (0 : ℝ) ≤ 0 ^ m 2 := pow_nonneg (by norm_num) _
    positivity
  · rw [site_mixture, hU]
    have h00 : (0 : ℝ) ≤ 0 ^ m 0 := pow_nonneg (by norm_num) _
    have h01 : (0 : ℝ) ≤ 0 ^ m 1 := pow_nonneg (by norm_num) _
    have h02 : (0 : ℝ) ≤ 0 ^ m 2 := pow_nonneg (by norm_num) _
    have hp : 0 ≤ ∏ i : Fin 3, (0 : Vec3) i ^ m i :=
      Finset.prod_nonneg (fun i _ => pow_nonneg (by simp) _)
    positivity
  · simp [siteFunctional, spinWeight]

theorem polynomial_functional_nonneg {α : Type*} [Fintype α]
    (s : α → Status) (p : MvPolynomial (α × Fin 3) ℕ) :
    0 ≤ productFunctional s (fun v =>
      MvPolynomial.eval₂ (Nat.castRingHom ℝ) (fun z => v z.1 z.2) p) := by
  classical
  unfold productFunctional
  simp_rw [MvPolynomial.eval₂_eq', Fintype.prod_prod_type, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_nonneg
  intro m hm
  have heq : (∑ σ : α → SpinLetter,
      (∏ x, spinWeight (s x) (σ x)) *
        ((p.coeff m : ℝ) * ∏ x, ∏ i, spinVector (σ x) i ^ m (x, i))) =
      (p.coeff m : ℝ) * ∏ x,
        siteFunctional (s x) (fun v => ∏ i, v i ^ m (x, i)) := by
    simp only [siteFunctional]
    rw [Fintype.prod_sum]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    rw [Finset.prod_mul_distrib]
    ring
  change 0 ≤ (∑ σ : α → SpinLetter,
      (∏ x, spinWeight (s x) (σ x)) *
        ((p.coeff m : ℝ) * ∏ x, ∏ i, spinVector (σ x) i ^ m (x, i)))
  rw [heq]
  exact mul_nonneg (Nat.cast_nonneg _) (Finset.prod_nonneg
    (fun x _ => site_monomial_nonneg (s x) (fun i => m (x, i))))

end AKLT.W.REC016
