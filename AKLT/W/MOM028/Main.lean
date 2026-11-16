import AKLT.Blueprint.Mom.NodesMean

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.MOM028

private lemma phi_sq : AKLT.Defs.goldenRatio ^ 2 = AKLT.Defs.goldenRatio + 1 := by
  unfold AKLT.Defs.goldenRatio
  have hs : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  nlinarith

private lemma radius_sq : AKLT.Defs.icoRadius ^ 2 = AKLT.Defs.goldenRatio + 2 := by
  unfold AKLT.Defs.icoRadius
  exact Real.sq_sqrt (by
    unfold AKLT.Defs.goldenRatio
    positivity)

private lemma radius_ne : AKLT.Defs.icoRadius ≠ 0 := by
  have h := radius_sq
  intro hz
  rw [hz] at h
  have hp : 0 < AKLT.Defs.goldenRatio := by
    unfold AKLT.Defs.goldenRatio
    positivity
  linarith

private lemma phi_four : AKLT.Defs.goldenRatio ^ 4 =
    3 * AKLT.Defs.goldenRatio + 2 := by
  calc
    AKLT.Defs.goldenRatio ^ 4 = (AKLT.Defs.goldenRatio ^ 2) ^ 2 := by ring
    _ = (AKLT.Defs.goldenRatio + 1) ^ 2 := congrArg (fun x : ℝ => x ^ 2) phi_sq
    _ = 3 * AKLT.Defs.goldenRatio + 2 := by nlinarith [phi_sq]

private lemma radius_four : AKLT.Defs.icoRadius ^ 4 =
    5 * AKLT.Defs.goldenRatio + 5 := by
  calc
    AKLT.Defs.icoRadius ^ 4 = (AKLT.Defs.icoRadius ^ 2) ^ 2 := by ring
    _ = (AKLT.Defs.goldenRatio + 2) ^ 2 := congrArg (fun x : ℝ => x ^ 2) radius_sq
    _ = 5 * AKLT.Defs.goldenRatio + 5 := by nlinarith [phi_sq]

private lemma radius_cube : AKLT.Defs.icoRadius ^ 3 =
    AKLT.Defs.icoRadius * (AKLT.Defs.goldenRatio + 2) := by
  calc
    AKLT.Defs.icoRadius ^ 3 = AKLT.Defs.icoRadius * AKLT.Defs.icoRadius ^ 2 := by ring
    _ = AKLT.Defs.icoRadius * (AKLT.Defs.goldenRatio + 2) := by rw [radius_sq]

private lemma siteU_eq_moment (f : Vec3 → ℝ) :
    AKLT.Defs.siteFunctional .U f = AKLT.Defs.moment f := by
  simp [AKLT.Defs.siteFunctional, Fintype.sum_option, AKLT.Defs.spinWeight,
    AKLT.Defs.spinVector, AKLT.Defs.moment, Finset.mul_sum]

private lemma denominator_formula (a : Fin 3 → Vec3) :
    AKLT.Defs.siteFunctional .U (AKLT.Defs.localProduct a) =
      1 + AKLT.Blueprint.Mom.tripleP a / 3 := by
  rw [siteU_eq_moment]
  unfold AKLT.Defs.moment AKLT.Defs.localProduct AKLT.Blueprint.Mom.tripleP
  simp [AKLT.Defs.IcoLetter, Fintype.sum_prod_type, Fin.sum_univ_three,
    Fin.prod_univ_three,
    AKLT.Defs.icoVector, AKLT.Defs.signValue, AKLT.Defs.dot]
  field_simp [radius_ne]
  ring_nf
  rw [phi_sq, radius_cube]
  ring

set_option maxRecDepth 4096 in
private lemma numerator_formula (a : Fin 3 → Vec3) (i : Fin 3) :
    15 * AKLT.Defs.siteFunctional .U
      (fun v => v i * AKLT.Defs.localProduct a v) =
        AKLT.Blueprint.Mom.tripleV a i := by
  fin_cases i
  all_goals
    rw [siteU_eq_moment]
    unfold AKLT.Defs.moment AKLT.Defs.localProduct AKLT.Blueprint.Mom.tripleV
      AKLT.Defs.dot
    simp [AKLT.Defs.IcoLetter, Fintype.sum_prod_type, Fin.sum_univ_three,
      Fin.prod_univ_three, AKLT.Defs.icoVector, AKLT.Defs.signValue]
    field_simp [radius_ne]
    ring_nf
    simp_rw [phi_four, radius_four, phi_sq, radius_sq]
    ring_nf
    simp_rw [phi_sq]
    ring

private lemma dot_rotate (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hR : R.transpose * R = 1) (a b : Vec3) :
    AKLT.Defs.dot (R.mulVec a) (R.mulVec b) = AKLT.Defs.dot a b := by
  change (R.mulVec a) ⬝ᵥ (R.mulVec b) = a ⬝ᵥ b
  rw [Matrix.dotProduct_mulVec (v := R.mulVec a) (A := R) (w := b)]
  rw [show Matrix.vecMul (R.mulVec a) R = R.transpose.mulVec (R.mulVec a) by
    simpa using Matrix.vecMul_transpose (A := R.transpose) (x := R.mulVec a)]
  rw [Matrix.mulVec_mulVec, hR]
  simp

private lemma tripleP_rotate (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hR : R.transpose * R = 1) (a : Fin 3 → Vec3) :
    AKLT.Blueprint.Mom.tripleP (fun j => R.mulVec (a j)) =
      AKLT.Blueprint.Mom.tripleP a := by
  unfold AKLT.Blueprint.Mom.tripleP
  rw [dot_rotate R hR (a 0) (a 1), dot_rotate R hR (a 0) (a 2),
    dot_rotate R hR (a 1) (a 2)]

private lemma tripleV_vector (a : Fin 3 → Vec3) :
    AKLT.Blueprint.Mom.tripleV a =
      5 • (a 0 + a 1 + a 2) +
        AKLT.Defs.dot (a 1) (a 2) • a 0 +
        AKLT.Defs.dot (a 0) (a 2) • a 1 +
        AKLT.Defs.dot (a 0) (a 1) • a 2 := by
  funext i
  simp [AKLT.Blueprint.Mom.tripleV, Pi.smul_apply, Pi.add_apply]
  ring

private lemma tripleV_rotate (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hR : R.transpose * R = 1) (a : Fin 3 → Vec3) :
    AKLT.Blueprint.Mom.tripleV (fun j => R.mulVec (a j)) =
      R.mulVec (AKLT.Blueprint.Mom.tripleV a) := by
  rw [tripleV_vector (fun j => R.mulVec (a j)), tripleV_vector a]
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul]
  rw [dot_rotate R hR (a 1) (a 2), dot_rotate R hR (a 0) (a 2),
    dot_rotate R hR (a 0) (a 1)]

private lemma normSq_triple_sum (a : Fin 3 → Vec3) :
    AKLT.Defs.normSq (a 0 + a 1 + a 2) =
      AKLT.Defs.normSq (a 0) + AKLT.Defs.normSq (a 1) +
        AKLT.Defs.normSq (a 2) + 2 * AKLT.Blueprint.Mom.tripleP a := by
  unfold AKLT.Defs.normSq AKLT.Blueprint.Mom.tripleP
  simp [AKLT.Defs.dot, Fin.sum_univ_three, Pi.add_apply]
  ring

private lemma denominator_pos (a : Fin 3 → Vec3)
    (ha : ∀ j, AKLT.Defs.normSq (a j) = 1) :
    0 < AKLT.Defs.siteFunctional .U (AKLT.Defs.localProduct a) := by
  rw [denominator_formula]
  have hs : AKLT.Defs.normSq (a 0 + a 1 + a 2) =
      3 + 2 * AKLT.Blueprint.Mom.tripleP a := by
    rw [normSq_triple_sum, ha 0, ha 1, ha 2]
    ring
  have hn : 0 ≤ AKLT.Defs.normSq (a 0 + a 1 + a 2) := by
    unfold AKLT.Defs.normSq AKLT.Defs.dot
    exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
  have heq : 1 + AKLT.Blueprint.Mom.tripleP a / 3 =
      1 / 2 + AKLT.Defs.normSq (a 0 + a 1 + a 2) / 6 := by
    rw [hs]
    ring
  rw [heq]
  linarith

private lemma localMean_formula (a : Fin 3 → Vec3)
    (ha : ∀ j, AKLT.Defs.normSq (a j) = 1) :
    AKLT.Defs.localMean .U a = fun i =>
      AKLT.Blueprint.Mom.tripleV a i /
        (15 * AKLT.Defs.siteFunctional .U (AKLT.Defs.localProduct a)) := by
  have hpos := denominator_pos a ha
  funext i
  change AKLT.Defs.siteFunctional .U
      (fun v => v i * AKLT.Defs.localProduct a v) /
      AKLT.Defs.siteFunctional .U (AKLT.Defs.localProduct a) = _
  have hn := numerator_formula a i
  have hnum : AKLT.Defs.siteFunctional .U
      (fun v => v i * AKLT.Defs.localProduct a v) =
        AKLT.Blueprint.Mom.tripleV a i / 15 := by
    linarith
  rw [hnum]
  field_simp [ne_of_gt hpos]

theorem main : AKLT.Blueprint.Mom.MeanCovarianceStatement := by
  intro a ha R hR
  let b : Fin 3 → Vec3 := fun j => R.mulVec (a j)
  have hb : ∀ j, AKLT.Defs.normSq (b j) = 1 := by
    intro j
    dsimp [b]
    calc
      AKLT.Defs.normSq (R.mulVec (a j)) = AKLT.Defs.normSq (a j) := by
        simpa [AKLT.Defs.normSq] using dot_rotate R hR (a j) (a j)
      _ = 1 := ha j
  let D : ℝ := AKLT.Defs.siteFunctional .U (AKLT.Defs.localProduct a)
  have hD : AKLT.Defs.siteFunctional .U (AKLT.Defs.localProduct b) = D := by
    dsimp [D, b]
    rw [denominator_formula, denominator_formula, tripleP_rotate R hR a]
  have hma : AKLT.Defs.localMean .U a = fun i =>
      AKLT.Blueprint.Mom.tripleV a i / (15 * D) := by
    simpa [D] using localMean_formula a ha
  have hmb : AKLT.Defs.localMean .U b = fun i =>
      AKLT.Blueprint.Mom.tripleV b i / (15 * D) := by
    rw [localMean_formula b hb, hD]
  have hscale : R.mulVec (fun i => AKLT.Blueprint.Mom.tripleV a i / (15 * D)) =
      (fun i => (R.mulVec (AKLT.Blueprint.Mom.tripleV a)) i / (15 * D)) := by
    ext i
    have hv : (fun j => AKLT.Blueprint.Mom.tripleV a j / (15 * D)) =
        (15 * D)⁻¹ • AKLT.Blueprint.Mom.tripleV a := by
      ext j
      simp [div_eq_mul_inv, smul_eq_mul, mul_comm]
    rw [hv]
    simpa [div_eq_mul_inv, mul_comm] using
      congrFun (Matrix.mulVec_smul R ((15 * D)⁻¹)
        (AKLT.Blueprint.Mom.tripleV a)) i
  rw [hmb, hma, tripleV_rotate R hR a]
  exact hscale.symm

#print axioms main

end AKLT.W.MOM028
