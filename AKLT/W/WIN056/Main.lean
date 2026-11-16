import AKLT.Blueprint.Win.NodesRemoval

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.WIN056

private theorem expectation_add {Ω : Type*} [Fintype Ω] (p : Weight Ω)
    (f g : Ω → ℝ) :
    expectation p (fun z => f z + g z) = expectation p f + expectation p g := by
  simp [expectation, Finset.sum_add_distrib, mul_add]

private theorem expectation_const {Ω : Type*} [Fintype Ω] (p : Weight Ω)
    (hp : Probability p) (c : ℝ) :
    expectation p (fun _ : Ω => c) = c := by
  unfold expectation
  calc
    (∑ z, p z * c) = (∑ z, p z) * c := by rw [Finset.sum_mul]
    _ = c := by rw [hp.2]; ring

private theorem expectation_div {Ω : Type*} [Fintype Ω] (p : Weight Ω)
    (f : Ω → ℝ) (c : ℝ) :
    expectation p (fun z => f z / c) = expectation p f / c := by
  unfold expectation
  simp_rw [div_eq_mul_inv, ← mul_assoc]
  rw [Finset.sum_mul]

theorem main : AKLT.Blueprint.Win.PolynomialLowerStatement := by
  classical
  intro D V p hp x hV hpair hquartic
  change (if V.card = 4 then (14 / 25 : ℝ) else 41 / 50) ≤
    expectation p (fun σ => AKLT.Blueprint.Win.removalPolynomial x V (extendIcoSpins σ))
  by_cases hcard : V.card = 4
  · have hexpect :
      expectation p (fun σ => AKLT.Blueprint.Win.removalPolynomial x V (extendIcoSpins σ)) =
        1 + expectation p (fun σ => AKLT.Blueprint.Win.pairSum V (extendIcoSpins σ)) / 3 +
          expectation p (fun σ => AKLT.Blueprint.Win.quartic x (extendIcoSpins σ)) / 15 := by
      calc
        _ = expectation p (fun _ : PlaneConfiguration D => 1) +
            expectation p (fun σ => AKLT.Blueprint.Win.pairSum V (extendIcoSpins σ) / 3) +
            expectation p (fun σ => AKLT.Blueprint.Win.quartic x (extendIcoSpins σ) / 15) := by
          simp [AKLT.Blueprint.Win.removalPolynomial, hcard]
          rw [expectation_add, expectation_add]
        _ = _ := by rw [expectation_const p hp, expectation_div, expectation_div]
    have hq : -(3 : ℝ) ≤
        expectation p (fun σ => AKLT.Blueprint.Win.quartic x (extendIcoSpins σ)) :=
      (abs_le.mp hquartic).1
    rw [hexpect]
    simp [hcard]
    have hpair' : -(18 / 25 : ℝ) ≤
        expectation p (fun σ => AKLT.Blueprint.Win.pairSum V (extendIcoSpins σ)) := by
      have := hpair
      rw [hcard] at this
      norm_num at this ⊢
      exact this
    nlinarith
  · have hsmall : V.card ≤ 3 := by omega
    have hexpect :
      expectation p (fun σ => AKLT.Blueprint.Win.removalPolynomial x V (extendIcoSpins σ)) =
        1 + expectation p (fun σ => AKLT.Blueprint.Win.pairSum V (extendIcoSpins σ)) / 3 := by
      calc
        _ = expectation p (fun _ : PlaneConfiguration D => 1) +
            expectation p (fun σ => AKLT.Blueprint.Win.pairSum V (extendIcoSpins σ) / 3) := by
          simp [AKLT.Blueprint.Win.removalPolynomial, hcard]
          rw [expectation_add]
        _ = _ := by rw [expectation_const p hp, expectation_div]
    rw [hexpect]
    simp [hcard]
    have hpair' : -(27 / 50 : ℝ) ≤
        expectation p (fun σ => AKLT.Blueprint.Win.pairSum V (extendIcoSpins σ)) := by
      have := hpair
      have hcard_real : (V.card : ℝ) ≤ 3 := by exact_mod_cast hsmall
      nlinarith
    nlinarith

end AKLT.W.WIN056

#print axioms AKLT.W.WIN056.main
