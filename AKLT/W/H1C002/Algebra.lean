module
public import AKLT.Cert.H1.Production.TopLeaves

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.H1C002

private abbrev Poly := MvPolynomial (Fin 20 × Fin 3) ℚ

/-- Inversion only multiplies a coefficient by an integer sign. -/
theorem coeff_invertPolynomial (I : Finset (Fin 20)) (p : Poly)
    (d : (Fin 20 × Fin 3) →₀ ℕ) :
    (invertPolynomial I p).coeff d = p.coeff d *
      ∏ v ∈ d.support, (if v.1 ∈ I then (-1 : ℚ) else 1) ^ d v := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq =>
      simp only [invertPolynomial, map_add, AddMonoidAlgebra.coeff_add,
        Finsupp.add_apply] at hp hq ⊢
      rw [hp, hq]
      ring
  | monomial d' c =>
      have hm : invertPolynomial I (MvPolynomial.monomial d' c) =
          MvPolynomial.monomial d'
            (c * ∏ v ∈ d'.support, (if v.1 ∈ I then (-1 : ℚ) else 1) ^ d' v) := by
        rw [invertPolynomial, MvPolynomial.eval₂Hom_monomial, MvPolynomial.monomial_eq]
        have hs (v : Fin 20 × Fin 3) :
            (if v.1 ∈ I then (-1 : Poly) else 1) =
              MvPolynomial.C (if v.1 ∈ I then (-1 : ℚ) else 1) := by
          split_ifs <;> simp
        simp_rw [hs]
        simp only [Finsupp.prod]
        simp_rw [mul_pow, ← map_pow (MvPolynomial.C : ℚ →+* Poly)]
        rw [Finset.prod_mul_distrib, ← map_prod (MvPolynomial.C : ℚ →+* Poly)]
        rw [← mul_assoc, ← map_mul (MvPolynomial.C : ℚ →+* Poly)]
      rw [hm, MvPolynomial.coeff_monomial]
      by_cases hd : d' = d
      · subst d'
        simp
      · simp [hd]

private def integerRationals : Subring ℚ := (Int.castRingHom ℚ).range

private theorem cast_mem_integerRationals (z : ℤ) : (z : ℚ) ∈ integerRationals :=
  ⟨z, rfl⟩

private theorem rationalPauli_integral (a : Fin 4) (i j : Fin 2) :
    (rationalPauli a i j).1 ∈ integerRationals ∧
      (rationalPauli a i j).2 ∈ integerRationals := by
  have h0 := integerRationals.zero_mem
  have h1 := integerRationals.one_mem
  have hn := integerRationals.neg_mem h1
  unfold rationalPauli
  split_ifs <;> exact ⟨by assumption, by assumption⟩

private theorem ratComplexMul_integral (a b : ℚ × ℚ)
    (ha : a.1 ∈ integerRationals ∧ a.2 ∈ integerRationals)
    (hb : b.1 ∈ integerRationals ∧ b.2 ∈ integerRationals) :
    (ratComplexMul a b).1 ∈ integerRationals ∧
      (ratComplexMul a b).2 ∈ integerRationals :=
  ⟨integerRationals.sub_mem (integerRationals.mul_mem ha.1 hb.1)
      (integerRationals.mul_mem ha.2 hb.2),
    integerRationals.add_mem (integerRationals.mul_mem ha.1 hb.2)
      (integerRationals.mul_mem ha.2 hb.1)⟩

private theorem fold_integral (l : List (ℚ × ℚ))
    (hl : ∀ z ∈ l, z.1 ∈ integerRationals ∧ z.2 ∈ integerRationals)
    (z : ℚ × ℚ) (hz : z.1 ∈ integerRationals ∧ z.2 ∈ integerRationals) :
    (l.foldl ratComplexMul z).1 ∈ integerRationals ∧
      (l.foldl ratComplexMul z).2 ∈ integerRationals := by
  induction l generalizing z with
  | nil => exact hz
  | cons a l ih =>
      exact ih (fun t ht => hl t (List.mem_cons_of_mem a ht)) _
        (ratComplexMul_integral z a hz (hl a (List.mem_cons_self)))

/-- A coefficientwise integral scale gives integral rational sector entries. -/
theorem sector_integral (π : PatternData) (r : Representation) (ε : ExchangeSigns π)
    (p : Poly) (k : ℚ) (hk : ∀ d, ∃ z : ℤ, k * p.coeff d = z)
    (a b : CentralBasis π r ε) :
    ∃ z : ℤ, k * rationalSectorEntry π r ε p a b = z := by
  classical
  have hop (σ τ : reductionVectors π r → Fin 2) :
      k * rationalOperatorEntry (reductionVectors π r) p σ τ ∈ integerRationals := by
    unfold rationalOperatorEntry
    rw [Finset.mul_sum]
    apply integerRationals.sum_mem
    intro t ht
    rw [← mul_assoc]
    apply integerRationals.mul_mem
    · obtain ⟨z, hz⟩ := hk (pauliExponent (reductionVectors π r) t)
      rw [hz]
      exact cast_mem_integerRationals z
    · apply (fold_integral _ ?_ (1, 0)
        ⟨integerRationals.one_mem, integerRationals.zero_mem⟩).1
      intro z hz
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hz
      exact rationalPauli_integral _ _ _
  have h : k * rationalSectorEntry π r ε p a b ∈ integerRationals := by
    unfold rationalSectorEntry
    rw [Finset.mul_sum]
    apply integerRationals.sum_mem
    intro σ hσ
    rw [Finset.mul_sum]
    apply integerRationals.sum_mem
    intro τ hτ
    have he : k * ((exchangeBasisVector π r ε a.val σ : ℚ) *
        rationalOperatorEntry (reductionVectors π r) p σ τ *
        (exchangeBasisVector π r ε b.val τ : ℚ)) =
        (exchangeBasisVector π r ε a.val σ : ℚ) *
          (k * rationalOperatorEntry (reductionVectors π r) p σ τ) *
          (exchangeBasisVector π r ε b.val τ : ℚ) := by ring
    rw [he]
    exact integerRationals.mul_mem
      (integerRationals.mul_mem (cast_mem_integerRationals _) (hop σ τ))
      (cast_mem_integerRationals _)
  obtain ⟨z, hz⟩ := h
  exact ⟨z, hz.symm⟩

/-- Flooring is exact at the cleared denominator, for either current or next. -/
theorem integerSectorMatrix_exact (π : PatternData) (r : Representation)
    (I : Finset (Fin 20)) (D₀ : ℕ) (hD : ClearsDenominator π r D₀)
    (ε : ExchangeSigns π) (next : Bool) (a b : CentralBasis π r ε) :
    (integerSectorMatrix π r ε I D₀ next a b : ℚ) =
      (if next then 5 else 3) * (D₀ : ℚ) * rationalSectorEntry π r ε
        (invertPolynomial I (reducedPolynomial π r next)) a b := by
  classical
  let k : ℚ := (if next then 5 else 3) * (D₀ : ℚ)
  have hc (d : (Fin 20 × Fin 3) →₀ ℕ) :
      ∃ z : ℤ, k * (reducedPolynomial π r next).coeff d = z := by
    by_cases hd : d ∈ (reducedPolynomial π r next).support
    · exact hD.2 next d hd
    · refine ⟨0, ?_⟩
      rw [MvPolynomial.notMem_support_iff.mp hd, mul_zero, Int.cast_zero]
  have hi (d : (Fin 20 × Fin 3) →₀ ℕ) :
      ∃ z : ℤ, k * (invertPolynomial I (reducedPolynomial π r next)).coeff d = z := by
    rw [coeff_invertPolynomial, ← mul_assoc]
    obtain ⟨z, hz⟩ := hc d
    rw [hz]
    have hs : (∏ v ∈ d.support, (if v.1 ∈ I then (-1 : ℚ) else 1) ^ d v) ∈
        integerRationals := by
      apply integerRationals.prod_mem
      intro v hv
      apply integerRationals.pow_mem
      split_ifs
      · exact integerRationals.neg_mem integerRationals.one_mem
      · exact integerRationals.one_mem
    obtain ⟨s, hs⟩ := hs
    refine ⟨z * s, ?_⟩
    rw [← hs]
    exact (Int.cast_mul z s).symm
  obtain ⟨z, hz⟩ := sector_integral π r ε _ k hi a b
  change (⌊k * rationalSectorEntry π r ε
    (invertPolynomial I (reducedPolynomial π r next)) a b⌋ : ℚ) = _
  change _ = k * rationalSectorEntry π r ε
    (invertPolynomial I (reducedPolynomial π r next)) a b
  rw [hz, Int.floor_intCast]

theorem rationalSectorEntry_sub (π : PatternData) (r : Representation)
    (ε : ExchangeSigns π) (p q : Poly) (a b : CentralBasis π r ε) :
    rationalSectorEntry π r ε (p - q) a b =
      rationalSectorEntry π r ε p a b - rationalSectorEntry π r ε q a b := by
  simp only [rationalSectorEntry, rationalOperatorEntry, MvPolynomial.coeff_sub,
    sub_mul, Finset.sum_sub_distrib, mul_sub]

theorem rationalSectorEntry_C_mul (π : PatternData) (r : Representation)
    (ε : ExchangeSigns π) (p : Poly) (k : ℚ) (a b : CentralBasis π r ε) :
    rationalSectorEntry π r ε (MvPolynomial.C k * p) a b =
      k * rationalSectorEntry π r ε p a b := by
  have hop (σ τ : reductionVectors π r → Fin 2) :
      rationalOperatorEntry (reductionVectors π r) (MvPolynomial.C k * p) σ τ =
        k * rationalOperatorEntry (reductionVectors π r) p σ τ := by
    simp only [rationalOperatorEntry, MvPolynomial.coeff_C_mul,
      Finset.mul_sum, mul_assoc]
  unfold rationalSectorEntry
  simp_rw [hop]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro τ hτ
  ring

theorem rationalSectorEntry_difference (π : PatternData) (r : Representation)
    (I : Finset (Fin 20)) (ε : ExchangeSigns π) (c : ℚ)
    (a b : CentralBasis π r ε) :
    rationalSectorEntry π r ε (invertPolynomial I (reducedDifference π r c)) a b =
      rationalSectorEntry π r ε (invertPolynomial I (reducedPolynomial π r false)) a b -
        c * rationalSectorEntry π r ε (invertPolynomial I (reducedPolynomial π r true)) a b := by
  have hi : invertPolynomial I (reducedDifference π r c) =
      invertPolynomial I (reducedPolynomial π r false) -
        MvPolynomial.C c * invertPolynomial I (reducedPolynomial π r true) := by
    simp [invertPolynomial, reducedDifference]
  rw [hi, rationalSectorEntry_sub, rationalSectorEntry_C_mul]

private def complexOf (z : ℚ × ℚ) : ℂ := (z.1 : ℂ) + (z.2 : ℂ) * Complex.I

private theorem complexOf_mul (z w : ℚ × ℚ) :
    complexOf (ratComplexMul z w) = complexOf z * complexOf w := by
  simp only [complexOf, ratComplexMul, Rat.cast_sub, Rat.cast_mul, Rat.cast_add]
  ring_nf
  simp [Complex.I_sq]
  ring

private theorem complexOf_rationalPauli (a : Fin 4) (i j : Fin 2) :
    complexOf (rationalPauli a i j) = pauli a i j := by
  fin_cases a <;> fin_cases i <;> fin_cases j <;>
    norm_num [complexOf, rationalPauli, pauli]

private theorem complexOf_fold (l : List (ℚ × ℚ)) (z : ℚ × ℚ) :
    complexOf (l.foldl ratComplexMul z) = complexOf z * (l.map complexOf).prod := by
  induction l generalizing z with
  | nil => simp
  | cons a l ih =>
      simp only [List.foldl_cons, ih, complexOf_mul, List.map_cons, List.prod_cons,
        mul_assoc]

private theorem rationalTensor_real (J : Finset (Fin 20)) (a : J → Fin 4)
    (σ τ : J → Fin 2) :
    ((((Finset.univ : Finset J).toList.map fun j => rationalPauli (a j) (σ j) (τ j)).foldl
      ratComplexMul (1, 0)).1 : ℝ) = (∏ j : J, pauli (a j) (σ j) (τ j)).re := by
  have h := complexOf_fold
    ((Finset.univ : Finset J).toList.map fun j => rationalPauli (a j) (σ j) (τ j)) (1, 0)
  simp only [complexOf, Rat.cast_one, Rat.cast_zero, zero_mul, add_zero, one_mul,
    List.map_map, Function.comp_def] at h
  have ht : (List.map
      (fun j : J => (rationalPauli (a j) (σ j) (τ j)).1 +
        (rationalPauli (a j) (σ j) (τ j)).2 * Complex.I)
      Finset.univ.toList).prod = ∏ j : J, pauli (a j) (σ j) (τ j) := by
    change (Finset.univ.toList.map (fun j => complexOf (rationalPauli (a j) (σ j) (τ j)))).prod = _
    simp_rw [complexOf_rationalPauli]
    exact Finset.prod_map_toList _ _
  rw [ht] at h
  have hr := congrArg Complex.re h
  simpa using hr

/-- The rational reconstruction is the real part of the complex operator. -/
theorem rationalOperatorEntry_real (J : Finset (Fin 20)) (p : Poly)
    (σ τ : J → Fin 2) :
    (rationalOperatorEntry J p σ τ : ℝ) = (pauliOperator J p σ τ).re := by
  simp only [rationalOperatorEntry, pauliOperator, Rat.cast_sum, Rat.cast_mul,
    Complex.re_sum, Complex.mul_re, Complex.ratCast_re, Complex.ratCast_im,
    zero_mul, sub_zero]
  apply Finset.sum_congr rfl
  intro a ha
  rw [rationalTensor_real]

/-- Entry reconstruction once imaginary cancellation has been established. -/
theorem complexSectorMatrix_exact (π : PatternData) (r : Representation)
    (ε : ExchangeSigns π) (p : Poly)
    (hreal : ∀ σ τ, (pauliOperator (reductionVectors π r) p σ τ).im = 0)
    (a b : CentralBasis π r ε) :
    complexSectorMatrix π r ε p a b = (rationalSectorEntry π r ε p a b : ℂ) := by
  have hop (σ τ : reductionVectors π r → Fin 2) :
      pauliOperator (reductionVectors π r) p σ τ =
        (rationalOperatorEntry (reductionVectors π r) p σ τ : ℂ) := by
    apply Complex.ext
    · simpa only [Complex.ratCast_re] using (rationalOperatorEntry_real _ p σ τ).symm
    · simpa only [Complex.ratCast_im] using hreal σ τ
  simp only [complexSectorMatrix, rationalSectorEntry, Rat.cast_sum, Rat.cast_mul,
    Rat.cast_intCast, hop]

end AKLT.W.H1C002

#print axioms AKLT.W.H1C002.coeff_invertPolynomial
#print axioms AKLT.W.H1C002.sector_integral
#print axioms AKLT.W.H1C002.integerSectorMatrix_exact
#print axioms AKLT.W.H1C002.rationalSectorEntry_sub
#print axioms AKLT.W.H1C002.rationalSectorEntry_C_mul
#print axioms AKLT.W.H1C002.rationalSectorEntry_difference
#print axioms AKLT.W.H1C002.rationalOperatorEntry_real
#print axioms AKLT.W.H1C002.complexSectorMatrix_exact
