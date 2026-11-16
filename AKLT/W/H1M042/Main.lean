import AKLT.Blueprint.H1.NodesStructure

noncomputable section

open scoped BigOperators ComplexOrder
open AKLT.Defs AKLT.Blueprint.H1

namespace AKLT.W.H1M042

private abbrev Var := Fin 20 × Fin 3

private def ySign (v : Var) : ℝ := if v.2 = 1 then -1 else 1

private def mapReal (p : VectorPolynomial) : MvPolynomial Var ℝ :=
  MvPolynomial.map (Rat.castHom ℝ) p

private def reflectPoly (p : MvPolynomial Var ℝ) : MvPolynomial Var ℝ :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun v => MvPolynomial.C (ySign v) * MvPolynomial.X v) p

private lemma reflectY_mulVec_coord (v : Vec3) (k : Fin 3) :
    (reflectY.mulVec v) k = (if k = 1 then -v k else v k) := by
  fin_cases k <;> simp [reflectY, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

private lemma reflectY_orthogonal : reflectY.transpose * reflectY = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [reflectY, Matrix.mul_apply, Fin.sum_univ_succ]

private lemma eval_mapReal (p : VectorPolynomial) (u : Fin 20 → Vec3) :
    evaluateReduced p u = MvPolynomial.eval (fun v : Var => u v.1 v.2) (mapReal p) := by
  exact (MvPolynomial.eval₂_eq_eval_map (Rat.castHom ℝ) _ p)

private lemma eval_reflectPoly (p : MvPolynomial Var ℝ) (x : Var → ℝ) :
    MvPolynomial.eval x (reflectPoly p) =
      MvPolynomial.eval (fun v => ySign v * x v) p := by
  rw [reflectPoly]
  change MvPolynomial.eval x
      (MvPolynomial.eval₂ MvPolynomial.C
        (fun v => MvPolynomial.C (ySign v) * MvPolynomial.X v) p) = _
  rw [← MvPolynomial.eval_assoc]
  apply congrArg (fun f : Var → ℝ => MvPolynomial.eval f p)
  funext v
  simp [Function.comp_apply]

private lemma coeff_reflectPoly (p : MvPolynomial Var ℝ) (d : Var →₀ ℕ) :
    (reflectPoly p).coeff d = p.coeff d *
      ∏ v ∈ d.support, ySign v ^ d v := by
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq =>
      rw [show reflectPoly (p + q) = reflectPoly p + reflectPoly q by
        simp [reflectPoly]]
      rw [AddMonoidAlgebra.coeff_add]
      change (reflectPoly p).coeff d + (reflectPoly q).coeff d = _
      rw [hp, hq]
      rw [show (p + q).coeff d = p.coeff d + q.coeff d by simp]
      ring_nf
  | monomial d' r =>
      have hmon : reflectPoly (MvPolynomial.monomial d' r) =
          MvPolynomial.monomial d' (r * ∏ v ∈ d'.support, ySign v ^ d' v) := by
        rw [reflectPoly, MvPolynomial.eval₂Hom_monomial, MvPolynomial.monomial_eq]
        simp only [Finsupp.prod]
        simp_rw [mul_pow]
        rw [Finset.prod_mul_distrib]
        have hconst : (∏ v ∈ d'.support,
              (MvPolynomial.C (ySign v ^ d' v) : MvPolynomial Var ℝ)) =
            (MvPolynomial.C : ℝ →+* MvPolynomial Var ℝ)
              (∏ v ∈ d'.support, ySign v ^ d' v) := by
          simp only [← map_prod
            (MvPolynomial.C : ℝ →+* MvPolynomial Var ℝ)]
        simp_rw [← map_pow (MvPolynomial.C : ℝ →+* MvPolynomial Var ℝ)]
        rw [hconst]
        rw [← mul_assoc]
        rw [← map_mul (MvPolynomial.C : ℝ →+* MvPolynomial Var ℝ)]
      rw [hmon, MvPolynomial.coeff_monomial]
      by_cases hd : d' = d
      · subst d'
        simp
      · simp [hd]

private lemma coeff_mapReal (p : VectorPolynomial) (d : Var →₀ ℕ) :
    (mapReal p).coeff d = (p.coeff d : ℝ) := by
  simp [mapReal, MvPolynomial.coeff_map]

private lemma exponent_y_count (J : Finset (Fin 20)) (a : J → Fin 4) :
    ∏ v ∈ (pauliExponent J a).support, ySign v ^ (pauliExponent J a) v =
      (-1 : ℝ) ^ pauliYCount J a := by
  classical
  have hsupp : ((pauliExponent J a).support.filter (fun v => v.2 = 1)) =
      (Finset.univ.filter (fun j : J => a j = 2)).image
        (fun j => (j.val, (1 : Fin 3))) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and,
      Finsupp.mem_support_iff]
    simp [pauliExponent, Finsupp.equivFunOnFinite]
    constructor
    · rintro ⟨⟨hJ, hv⟩, hv2⟩
      refine ⟨v.1, ⟨hJ, ?_⟩, Prod.ext rfl hv2.symm⟩
      apply Fin.ext
      simpa [hv2] using hv
    · rintro ⟨j, ⟨hJ, hj⟩, hp⟩
      have hfirst := congrArg Prod.fst hp
      have hsecond := congrArg Prod.snd hp
      have hJv : v.1 ∈ J := by rw [← hfirst]; exact hJ
      have hsub : (⟨v.1, hJv⟩ : J) = ⟨j, hJ⟩ := Subtype.ext hfirst.symm
      refine ⟨⟨hJv, ?_⟩, hsecond.symm⟩
      have hA : a ⟨v.1, hJv⟩ = 2 := by rw [hsub]; exact hj
      change (a (⟨v.1, hJv⟩ : J)).val = v.2.val + 1
      rw [← hsecond]
      simpa using congrArg Fin.val hA
  have hinj : Function.Injective (fun j : J => (j.val, (1 : Fin 3))) := by
    intro j k h
    exact Subtype.ext (congrArg Prod.fst h)
  have hval : ∀ v ∈ (pauliExponent J a).support, (pauliExponent J a) v = 1 := by
    intro v hv
    simp only [Finsupp.mem_support_iff] at hv
    simp [pauliExponent, Finsupp.equivFunOnFinite] at hv ⊢
    split_ifs <;> simp_all
  calc
    ∏ v ∈ (pauliExponent J a).support, ySign v ^ (pauliExponent J a) v
        = ∏ v ∈ (pauliExponent J a).support, if v.2 = 1 then -1 else 1 := by
            apply Finset.prod_congr rfl
            intro v hv
            simp [ySign, hval v hv]
    _ = (-1 : ℝ) ^ ((pauliExponent J a).support.filter (fun v => v.2 = 1)).card := by
          simp [Finset.prod_ite]
    _ = (-1 : ℝ) ^ pauliYCount J a := by
          rw [hsupp, Finset.card_image_of_injective _ hinj]
          rfl

theorem main : AKLT.Blueprint.H1.ReflectionParityStatement := by
  classical
  intro J p _ _ hinv a hodd
  have hpoly : reflectPoly (mapReal p) = mapReal p := by
    apply MvPolynomial.funext
    intro x
    let u : Fin 20 → Vec3 := fun j k => x (j, k)
    have hcov := hinv reflectY reflectY_orthogonal u
    have hleft := eval_reflectPoly (mapReal p) x
    have hu : (fun v : Var => ySign v * x v) =
        (fun v => (reflectY.mulVec (u v.1)) v.2) := by
      funext v
      simp [ySign, u, reflectY_mulVec_coord]
    rw [hu] at hleft
    rw [eval_mapReal] at hcov
    rw [eval_mapReal] at hcov
    exact hleft.trans hcov
  have hc := congrArg (fun q : MvPolynomial Var ℝ => q.coeff (pauliExponent J a)) hpoly
  rw [coeff_reflectPoly, coeff_mapReal] at hc
  rw [exponent_y_count] at hc
  have hsign : (-1 : ℝ) ^ pauliYCount J a = -1 := by
    rcases hodd with ⟨n, hn⟩
    rw [hn]
    rw [pow_add, pow_mul]
    norm_num
  rw [hsign] at hc
  have hz : (p.coeff (pauliExponent J a) : ℝ) = 0 := by linarith
  exact_mod_cast hz

end AKLT.W.H1M042

end
