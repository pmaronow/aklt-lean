module
public import AKLT.Blueprint.Q.NodesTight

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Q

namespace AKLT.W.Q013

private theorem sqrt5_sq : (Real.sqrt 5 : ℝ) ^ 2 = 5 := by
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]

private theorem phi_sq : goldenRatio ^ 2 = goldenRatio + 1 := by
  unfold goldenRatio
  nlinarith [sqrt5_sq]

private theorem radius_sq : icoRadius ^ 2 = goldenRatio + 2 := by
  unfold icoRadius
  rw [Real.sq_sqrt (by unfold goldenRatio; positivity)]

private theorem icoThird_even_two :
    (1 / 12 : ℝ) * ∑ a : IcoLetter, (icoVector a 2) ^ 2 = 1 / 3 := by
  simp only [Fintype.sum_prod_type]
  simp [icoVector, signValue, Fin.sum_univ_succ]
  have hr0 : icoRadius ≠ 0 := by
    unfold icoRadius
    apply ne_of_gt
    apply Real.sqrt_pos.2
    unfold goldenRatio
    positivity
  field_simp [hr0]
  simp_rw [radius_sq, phi_sq]
  ring

private theorem icoThird_odd_one :
    (1 / 12 : ℝ) * ∑ a : IcoLetter, icoVector a 2 = 0 := by
  simp only [Fintype.sum_prod_type]
  simp [icoVector, signValue, Fin.sum_univ_succ]
  ring

private theorem icoThird_odd_three :
    (1 / 12 : ℝ) * ∑ a : IcoLetter, (icoVector a 2) ^ 3 = 0 := by
  simp only [Fintype.sum_prod_type]
  simp [icoVector, signValue, Fin.sum_univ_succ]
  ring

private theorem icoThird_even_four :
    (1 / 12 : ℝ) * ∑ a : IcoLetter, (icoVector a 2) ^ 4 = 1 / 5 := by
  simp only [Fintype.sum_prod_type]
  simp [icoVector, signValue, Fin.sum_univ_succ]
  have hr0 : icoRadius ≠ 0 := by
    unfold icoRadius
    apply ne_of_gt
    apply Real.sqrt_pos.2
    unfold goldenRatio
    positivity
  field_simp [hr0]
  have hp4 : goldenRatio ^ 4 = 3 * goldenRatio + 2 := by
    calc
      goldenRatio ^ 4 = (goldenRatio ^ 2) ^ 2 := by ring
      _ = (goldenRatio + 1) ^ 2 := by rw [phi_sq]
      _ = 3 * goldenRatio + 2 := by nlinarith [phi_sq]
  have hr4 : icoRadius ^ 4 = 5 * (goldenRatio + 1) := by
    calc
      icoRadius ^ 4 = (icoRadius ^ 2) ^ 2 := by ring
      _ = (goldenRatio + 2) ^ 2 := by rw [radius_sq]
      _ = 5 * (goldenRatio + 1) := by nlinarith [phi_sq]
  simp_rw [hp4, hr4]
  ring

private def cThirdMoment (n : ℕ) : ℂ :=
  (1 / 12 : ℂ) * ∑ a : IcoLetter, (icoVector a 2 : ℂ) ^ n

private theorem complexMoment_X2_pow (n : ℕ) :
    complexMoment (MvPolynomial.X (2 : Fin 3) ^ n) = cThirdMoment n := by
  simp [complexMoment, cThirdMoment]

private theorem cThirdMoment_zero : cThirdMoment 0 = 1 := by
  norm_num [cThirdMoment, IcoLetter, Fintype.card_prod]

private theorem cThirdMoment_one : cThirdMoment 1 = 0 := by
  have h := congrArg (fun x : ℝ => (x : ℂ)) icoThird_odd_one
  simpa [cThirdMoment, map_mul, map_sum, map_pow] using h

private theorem cThirdMoment_two : cThirdMoment 2 = (1 / 3 : ℂ) := by
  have h := congrArg (fun x : ℝ => (x : ℂ)) icoThird_even_two
  simpa [cThirdMoment, map_mul, map_sum, map_pow] using h

private theorem cThirdMoment_three : cThirdMoment 3 = 0 := by
  have h := congrArg (fun x : ℝ => (x : ℂ)) icoThird_odd_three
  simpa [cThirdMoment, map_mul, map_sum, map_pow] using h

private theorem cThirdMoment_four : cThirdMoment 4 = (1 / 5 : ℂ) := by
  have h := congrArg (fun x : ℝ => (x : ℂ)) icoThird_even_four
  simpa [cThirdMoment, map_mul, map_sum, map_pow] using h

private theorem complexMoment_add (p q : MvPolynomial (Fin 3) ℂ) :
    complexMoment (p + q) = complexMoment p + complexMoment q := by
  simp [complexMoment, MvPolynomial.eval_add, Finset.sum_add_distrib, mul_add]

private theorem complexMoment_C (c : ℂ) :
    complexMoment (MvPolynomial.C c) = c := by
  norm_num [complexMoment, IcoLetter, Fintype.card_prod]
  ring

private theorem complexMoment_one :
    complexMoment (1 : MvPolynomial (Fin 3) ℂ) = 1 := by
  change complexMoment (MvPolynomial.C (1 : ℂ)) = 1
  exact complexMoment_C 1

private theorem complexMoment_C_mul (c : ℂ) (p : MvPolynomial (Fin 3) ℂ) :
    complexMoment (MvPolynomial.C c * p) = c * complexMoment p := by
  unfold complexMoment
  simp only [MvPolynomial.eval_mul, MvPolynomial.eval_C]
  calc
    (1 / 12 : ℂ) * ∑ a, c * MvPolynomial.eval (fun i => (icoVector a i : ℂ)) p =
        (1 / 12 : ℂ) * (c * ∑ a, MvPolynomial.eval (fun i => (icoVector a i : ℂ)) p) := by
          congr 1
          rw [← Finset.mul_sum]
    _ = c * ((1 / 12 : ℂ) * ∑ a, MvPolynomial.eval (fun i => (icoVector a i : ℂ)) p) := by ring

private theorem complexMoment_X2_pow_value (n : ℕ) (h : n ≤ 4) :
    complexMoment (MvPolynomial.X (2 : Fin 3) ^ n) =
      if n = 0 then 1 else if n = 1 then 0 else if n = 2 then 1 / 3
        else if n = 3 then 0 else 1 / 5 := by
  interval_cases n
  · simpa [complexMoment_C, cThirdMoment_zero] using complexMoment_X2_pow 0
  · simpa [cThirdMoment_one] using complexMoment_X2_pow 1
  · simpa [cThirdMoment_two] using complexMoment_X2_pow 2
  · simpa [cThirdMoment_three] using complexMoment_X2_pow 3
  · simpa [cThirdMoment_four] using complexMoment_X2_pow 4

private abbrev X3 : MvPolynomial (Fin 3) ℂ := MvPolynomial.X (2 : Fin 3)

private theorem complexMoment_neg (p : MvPolynomial (Fin 3) ℂ) :
    complexMoment (-p) = -complexMoment p := by
  simp [complexMoment, MvPolynomial.eval_neg, Finset.sum_neg_distrib, mul_neg]

private theorem complexMoment_X3 : complexMoment X3 = 0 := by
  simpa [X3] using complexMoment_X2_pow_value 1 (by norm_num)

private theorem complexMoment_X3_sq : complexMoment (X3 ^ 2) = (1 / 3 : ℂ) := by
  simpa [X3] using complexMoment_X2_pow_value 2 (by norm_num)

private theorem complexMoment_X3_cube : complexMoment (X3 ^ 3) = 0 := by
  simpa [X3] using complexMoment_X2_pow_value 3 (by norm_num)

private theorem complexMoment_X3_fourth : complexMoment (X3 ^ 4) = (1 / 5 : ℂ) := by
  simpa [X3] using complexMoment_X2_pow_value 4 (by norm_num)

private theorem cMoment_diag0 : complexMoment ((1 + X3) ^ 4) = (16 / 5 : ℂ) := by
  have hp : (1 + X3) ^ 4 =
      1 + X3 + X3 + X3 + X3 + X3 ^ 2 + X3 ^ 2 + X3 ^ 2 + X3 ^ 2 + X3 ^ 2 + X3 ^ 2 +
        X3 ^ 3 + X3 ^ 3 + X3 ^ 3 + X3 ^ 3 + X3 ^ 4 := by ring
  rw [hp]
  simp [complexMoment_add, complexMoment_one, complexMoment_X3, complexMoment_X3_sq,
    complexMoment_X3_cube, complexMoment_X3_fourth]
  norm_num

private theorem cMoment_diag1 :
    complexMoment ((1 + X3) ^ 3 * (1 - X3)) = (4 / 5 : ℂ) := by
  have hp : (1 + X3) ^ 3 * (1 - X3) =
      1 + X3 + X3 + (-X3 ^ 3) + (-X3 ^ 3) + (-X3 ^ 4) := by ring
  rw [hp]
  simp [complexMoment_add, complexMoment_neg, complexMoment_one, complexMoment_X3,
    complexMoment_X3_cube, complexMoment_X3_fourth]
  norm_num

private theorem cMoment_diag2 :
    complexMoment ((1 + X3) ^ 2 * (1 - X3) ^ 2) = (8 / 15 : ℂ) := by
  have hp : (1 + X3) ^ 2 * (1 - X3) ^ 2 =
      1 + (-X3 ^ 2) + (-X3 ^ 2) + X3 ^ 4 := by ring
  rw [hp]
  simp [complexMoment_add, complexMoment_neg, complexMoment_one, complexMoment_X3_sq,
    complexMoment_X3_fourth]
  norm_num

private theorem cMoment_diag3 :
    complexMoment ((1 + X3) * (1 - X3) ^ 3) = (4 / 5 : ℂ) := by
  have hp : (1 + X3) * (1 - X3) ^ 3 =
      1 + (-X3) + (-X3) + X3 ^ 3 + X3 ^ 3 + (-X3 ^ 4) := by ring
  rw [hp]
  simp [complexMoment_add, complexMoment_neg, complexMoment_one, complexMoment_X3,
    complexMoment_X3_cube, complexMoment_X3_fourth]
  norm_num

private theorem cMoment_diag4 :
    complexMoment ((1 - X3) ^ 4) = (16 / 5 : ℂ) := by
  have hp : (1 - X3) ^ 4 =
      1 + (-X3) + (-X3) + (-X3) + (-X3) + X3 ^ 2 + X3 ^ 2 + X3 ^ 2 + X3 ^ 2 + X3 ^ 2 + X3 ^ 2 +
        (-X3 ^ 3) + (-X3 ^ 3) + (-X3 ^ 3) + (-X3 ^ 3) + X3 ^ 4 := by ring
  rw [hp]
  simp [complexMoment_add, complexMoment_neg, complexMoment_one, complexMoment_X3,
    complexMoment_X3_sq, complexMoment_X3_cube, complexMoment_X3_fourth]
  norm_num

theorem main : AKLT.Blueprint.Q.QuarticDiagonalStatement := by
  intro j
  fin_cases j <;>
    norm_num [quarticKernel, X3, mul_assoc, complexMoment_C_mul, cMoment_diag0,
      cMoment_diag1, cMoment_diag2, cMoment_diag3, cMoment_diag4, Nat.choose]

end AKLT.W.Q013
