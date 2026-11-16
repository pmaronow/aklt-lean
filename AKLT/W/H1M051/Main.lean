import AKLT.Blueprint.H1.NodesStructure

set_option maxHeartbeats 600000

noncomputable section
open scoped BigOperators ComplexOrder
open AKLT.Defs

namespace AKLT.W.H1M051

open AKLT.Blueprint.H1

abbrev LocalPoly := LocalPolynomial
abbrev VecPoly := VectorPolynomial

def internalExponent (m : LocalVariable →₀ ℕ) : (Plane × Fin 3) →₀ ℕ :=
  Finsupp.comapDomain Sum.inl m Sum.inl_injective.injOn

def externalExponent (m : LocalVariable →₀ ℕ) : (Fin 20 × Fin 3) →₀ ℕ :=
  Finsupp.comapDomain Sum.inr m Sum.inr_injective.injOn

def inversionSignQ (I : Finset (Fin 20)) (e : (Fin 20 × Fin 3) →₀ ℕ) : ℚ :=
  ∏ v ∈ e.support, (if v.1 ∈ I then (-1 : ℚ) else 1) ^ e v

def inversionSignR (I : Finset (Fin 20)) (e : (Fin 20 × Fin 3) →₀ ℕ) : ℝ :=
  ∏ v ∈ e.support, (if v.1 ∈ I then (-1 : ℝ) else 1) ^ e v

def internalSpinMonomial (m : LocalVariable →₀ ℕ) (V : Finset Plane)
    (n : V → SpinLetter) : ℝ :=
  ∏ x : V, ∏ k : Fin 3,
    (supportSpins V n x.1) k ^ m (.inl (x.1, k))

lemma invertPolynomial_monomial (I : Finset (Fin 20)) (e : (Fin 20 × Fin 3) →₀ ℕ) (c : ℚ) :
    invertPolynomial I (MvPolynomial.monomial e c) =
      MvPolynomial.monomial e (c * inversionSignQ I e) := by
  classical
  simp only [invertPolynomial, MvPolynomial.eval₂Hom_monomial, inversionSignQ,
    Finsupp.prod, mul_pow, Finset.prod_mul_distrib, MvPolynomial.prod_X_pow_eq_monomial]
  have hsign : (∏ x ∈ e.support,
      (if x.1 ∈ I then (-1 : MvPolynomial (Fin 20 × Fin 3) ℚ) else 1) ^ e x) =
      MvPolynomial.C (∏ x ∈ e.support,
        (if x.1 ∈ I then (-1 : ℚ) else 1) ^ e x) := by
    calc
      _ = ∏ x ∈ e.support, MvPolynomial.C
          ((if x.1 ∈ I then (-1 : ℚ) else 1) ^ e x) := by
        apply Finset.prod_congr rfl
        intro x hx
        by_cases hi : x.1 ∈ I <;> simp [hi]
      _ = MvPolynomial.C (∏ x ∈ e.support,
          (if x.1 ∈ I then (-1 : ℚ) else 1) ^ e x) := by
        symm
        exact map_prod MvPolynomial.C _ _
  rw [hsign]
  rw [← mul_assoc, ← MvPolynomial.C_mul, MvPolynomial.C_mul_monomial]
  simp

lemma invertRealPolynomial_monomial (I : Finset (Fin 20)) (e : (Fin 20 × Fin 3) →₀ ℕ) (c : ℝ) :
    invertRealPolynomial I (MvPolynomial.monomial e c) =
      MvPolynomial.monomial e (c * inversionSignR I e) := by
  classical
  simp only [invertRealPolynomial, MvPolynomial.eval₂Hom_monomial, inversionSignR,
    Finsupp.prod, mul_pow, Finset.prod_mul_distrib, MvPolynomial.prod_X_pow_eq_monomial]
  have hsign : (∏ x ∈ e.support,
      (if x.1 ∈ I then (-1 : MvPolynomial (Fin 20 × Fin 3) ℝ) else 1) ^ e x) =
      MvPolynomial.C (∏ x ∈ e.support,
        (if x.1 ∈ I then (-1 : ℝ) else 1) ^ e x) := by
    calc
      _ = ∏ x ∈ e.support, MvPolynomial.C
          ((if x.1 ∈ I then (-1 : ℝ) else 1) ^ e x) := by
        apply Finset.prod_congr rfl
        intro x hx
        by_cases hi : x.1 ∈ I <;> simp [hi]
      _ = MvPolynomial.C (∏ x ∈ e.support,
          (if x.1 ∈ I then (-1 : ℝ) else 1) ^ e x) := by
        symm
        exact map_prod MvPolynomial.C _ _
  rw [hsign]
  rw [← mul_assoc, ← MvPolynomial.C_mul, MvPolynomial.C_mul_monomial]
  simp

lemma internalExponent_supported (V : Finset Plane) (m : LocalVariable →₀ ℕ)
    (h : ∀ x : Plane, x ∉ V → ∀ k : Fin 3, m (.inl (x,k)) = 0) :
    ∀ a ∈ (internalExponent m).support, a.1 ∈ V := by
  intro a ha
  have hm : m (.inl a) ≠ 0 := by
    have hmem := (Finsupp.mem_support_iff.mp ha)
    simpa [internalExponent] using hmem
  by_contra hout
  exact hm (h a.1 hout a.2)

lemma internalExponent_prod (V : Finset Plane) (m : LocalVariable →₀ ℕ)
    (n : V → SpinLetter)
    (h : ∀ x : Plane, x ∉ V → ∀ k : Fin 3, m (.inl (x,k)) = 0) :
    (internalExponent m).prod (fun a e => (supportSpins V n a.1) a.2 ^ e) =
      internalSpinMonomial m V n := by
  classical
  let q := internalExponent m
  have hsub : q.support ⊆ V.product Finset.univ := by
    intro a ha
    apply Finset.mem_product.mpr
    exact ⟨internalExponent_supported V m h a ha, Finset.mem_univ _⟩
  calc
    q.prod (fun a e => (supportSpins V n a.1) a.2 ^ e) =
        ∏ a ∈ q.support, (supportSpins V n a.1) a.2 ^ q a := rfl
    _ = ∏ a ∈ V.product Finset.univ, (supportSpins V n a.1) a.2 ^ q a := by
      apply Finset.prod_subset hsub
      intro a ha hnot
      have hzero : q a = 0 := Finsupp.notMem_support_iff.mp hnot
      simp [hzero]
    _ = internalSpinMonomial m V n := by
      have hp := Finset.prod_product V (Finset.univ : Finset (Fin 3))
        (fun a : Plane × Fin 3 => (supportSpins V n a.1) a.2 ^ q a)
      have ha := (Finset.prod_coe_sort V (fun x : Plane =>
        ∏ k : Fin 3, (supportSpins V n x) k ^ q (x,k))).symm
      simpa [internalSpinMonomial, q, internalExponent,
        Finsupp.comapDomain_apply, supportSpins] using hp.trans ha

lemma specializeInternal_monomial (V : Finset Plane) (m : LocalVariable →₀ ℕ) (c : ℚ)
    (n : V → SpinLetter)
    (h : ∀ x : Plane, x ∉ V → ∀ k : Fin 3, m (.inl (x,k)) = 0) :
    specializeInternal (MvPolynomial.monomial m c) (supportSpins V n) =
      MvPolynomial.monomial (externalExponent m)
        ((c : ℝ) * internalSpinMonomial m V n) := by
  classical
  unfold specializeInternal
  rw [MvPolynomial.eval₂Hom_monomial]
  conv_lhs =>
    arg 2
    rw [← Finsupp.comapDomain_sumElim_comapDomain m, Finsupp.prod_sumElim]
  conv_lhs =>
    arg 2
    arg 1
    change (internalExponent m).prod (fun a e =>
      (MvPolynomial.C (supportSpins V n a.1 a.2) : MvPolynomial (Fin 20 × Fin 3) ℝ) ^ e)
  conv_lhs =>
    arg 2
    arg 2
    change (externalExponent m).prod (fun a e =>
      (MvPolynomial.X a : MvPolynomial (Fin 20 × Fin 3) ℝ) ^ e)
  have hint : (internalExponent m).prod (fun a e =>
      (MvPolynomial.C (supportSpins V n a.1 a.2) : MvPolynomial (Fin 20 × Fin 3) ℝ) ^ e) =
      MvPolynomial.C ((internalExponent m).prod (fun a e =>
        supportSpins V n a.1 a.2 ^ e)) := by
    simp only [Finsupp.prod]
    calc
      _ = ∏ a ∈ (internalExponent m).support,
            MvPolynomial.C (supportSpins V n a.1 a.2 ^ (internalExponent m) a) := by
          apply Finset.prod_congr rfl
          intro a ha
          simp
      _ = MvPolynomial.C (∏ a ∈ (internalExponent m).support,
            supportSpins V n a.1 a.2 ^ (internalExponent m) a) := by rw [← map_prod]
  conv_lhs =>
    arg 2
    arg 1
    rw [hint]
  conv_lhs =>
    arg 2
    arg 1
    arg 2
    rw [internalExponent_prod V m n h]
  conv_lhs =>
    arg 2
    arg 2
    change ∏ a ∈ (externalExponent m).support,
      (MvPolynomial.X a : MvPolynomial (Fin 20 × Fin 3) ℝ) ^ (externalExponent m) a
    rw [MvPolynomial.prod_X_pow_eq_monomial]
  simp [MvPolynomial.C_mul_monomial]

lemma momentProductSum (hMom : MonomialMoments) (V : Finset Plane) (s : Plane → Status)
    (hStatus : ∀ x ∈ V, s x = .U ∨ s x = .D)
    (m : LocalVariable →₀ ℕ)
    (hDegree : ∀ x : Plane, (∑ k : Fin 3, m (.inl (x,k))) ≤ 4)
    (_nSupport : ∀ x : Plane, x ∉ V → ∀ k : Fin 3, m (.inl (x,k)) = 0) :
    (∑ n : V → SpinLetter,
      (∏ x : V, spinWeight (s x.1) (n x)) * internalSpinMonomial m V n) =
      ∏ x : V, (rationalStatusMoment (s x.1) (fun k => m (.inl (x.1,k))) : ℝ) := by
  classical
  calc
    _ = ∑ n : V → SpinLetter, ∏ x : V,
          spinWeight (s x.1) (n x) *
            ∏ k : Fin 3, (spinVector (n x)) k ^ m (.inl (x.1,k)) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [internalSpinMonomial, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro x hx
      simp [supportSpins, x.2]
    _ = ∏ x : V, ∑ a : SpinLetter,
          spinWeight (s x.1) a *
            ∏ k : Fin 3, (spinVector a) k ^ m (.inl (x.1,k)) := by
      simpa using (Fintype.prod_sum
        (fun (x : V) (a : SpinLetter) =>
          spinWeight (s x.1) a *
            ∏ k : Fin 3, (spinVector a) k ^ m (.inl (x.1,k)))).symm
    _ = ∏ x : V, (rationalStatusMoment (s x.1) (fun k => m (.inl (x.1,k))) : ℝ) := by
      apply Finset.prod_congr rfl
      intro x hx
      have hsx : s x.1 = .U ∨ s x.1 = .D := hStatus x.1 x.2
      have hmoment := hMom (fun k : Fin 3 => m (.inl (x.1,k))) (hDegree x.1) (s x.1) hsx
      simpa [siteFunctional] using hmoment

lemma specializeInternal_as_sum (V : Finset Plane) (p : LocalPoly) (n : V → SpinLetter)
    (hNoOut : ∀ m ∈ p.support, ∀ x : Plane, x ∉ V → ∀ k : Fin 3, m (.inl (x,k)) = 0) :
    specializeInternal p (supportSpins V n) =
      ∑ m ∈ p.support, MvPolynomial.monomial (externalExponent m)
        ((p.coeff m : ℝ) * internalSpinMonomial m V n) := by
  classical
  calc
    specializeInternal p (supportSpins V n) =
        specializeInternal (∑ m ∈ p.support, MvPolynomial.monomial m (p.coeff m))
          (supportSpins V n) := by rw [← MvPolynomial.as_sum p]
    _ = ∑ m ∈ p.support,
        specializeInternal (MvPolynomial.monomial m (p.coeff m)) (supportSpins V n) := by
      simp only [specializeInternal]
      rw [map_sum]
    _ = ∑ m ∈ p.support, MvPolynomial.monomial (externalExponent m)
        ((p.coeff m : ℝ) * internalSpinMonomial m V n) := by
      apply Finset.sum_congr rfl
      intro m hm
      exact specializeInternal_monomial V m (p.coeff m) n (hNoOut m hm)

lemma map_contractSpins_expansion (V : Finset Plane) (s : Plane → Status)
    (p : LocalPoly) :
    MvPolynomial.map (Rat.castHom ℝ) (contractSpins V s p) =
      ∑ m ∈ p.support, MvPolynomial.monomial (externalExponent m)
        ((p.coeff m : ℝ) * ∏ x ∈ V,
          (rationalStatusMoment (s x) (fun k => m (.inl (x,k))) : ℝ)) := by
  classical
  simp [contractSpins, externalExponent, MvPolynomial.map_monomial, map_sum, map_mul, map_prod]

lemma monomialMomentInterchange (hMom : MonomialMoments) (V : Finset Plane)
    (s : Plane → Status) (hStatus : ∀ x ∈ V, s x = .U ∨ s x = .D)
    (m : LocalVariable →₀ ℕ) (c : ℝ)
    (hDegree : ∀ x : Plane, (∑ k : Fin 3, m (.inl (x,k))) ≤ 4)
    (hNoOut : ∀ x : Plane, x ∉ V → ∀ k : Fin 3, m (.inl (x,k)) = 0) :
    MvPolynomial.monomial (externalExponent m)
        (c * ∏ x ∈ V, (rationalStatusMoment (s x) (fun k => m (.inl (x,k))) : ℝ)) =
      ∑ n : V → SpinLetter, (∏ x : V, spinWeight (s x.1) (n x)) •
        MvPolynomial.monomial (externalExponent m)
          (c * internalSpinMonomial m V n) := by
  classical
  have hmom := momentProductSum hMom V s hStatus m hDegree hNoOut
  have hprod : (∏ x ∈ V,
      (rationalStatusMoment (s x) (fun k => m (.inl (x,k))) : ℝ)) =
      ∏ x : V, (rationalStatusMoment (s x.1) (fun k => m (.inl (x.1,k))) : ℝ) := by
    rw [← Finset.prod_coe_sort V (fun x =>
      (rationalStatusMoment (s x) (fun k => m (.inl (x,k))) : ℝ))]
  rw [hprod]
  apply MvPolynomial.ext
  intro d
  by_cases hd : externalExponent m = d
  · subst d
    simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, MvPolynomial.coeff_monomial]
    simp only [ite_true]
    calc
      c * ∏ x : V,
          (rationalStatusMoment (s x.1) (fun k => m (.inl (x.1,k))) : ℝ) =
          c * ∑ n : V → SpinLetter,
            (∏ x : V, spinWeight (s x.1) (n x)) * internalSpinMonomial m V n := by
        rw [hmom]
      _ = ∑ n : V → SpinLetter,
            (∏ x : V, spinWeight (s x.1) (n x)) *
              (c * internalSpinMonomial m V n) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n hn
        ring
  · simp [MvPolynomial.coeff_monomial, hd]

lemma contractSpinMap_interchange (hMom : MonomialMoments) (V : Finset Plane)
    (s : Plane → Status) (hStatus : ∀ x ∈ V, s x = .U ∨ s x = .D)
    (p : LocalPoly) (hInt : InternalAdmissible V p) :
    MvPolynomial.map (Rat.castHom ℝ) (contractSpins V s p) =
      ∑ n : V → SpinLetter, (∏ x : V, spinWeight (s x.1) (n x)) •
        specializeInternal p (supportSpins V n) := by
  classical
  rcases hInt with ⟨hNoOut, hDegree⟩
  rw [map_contractSpins_expansion]
  simp_rw [specializeInternal_as_sum V p _ hNoOut, Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  exact monomialMomentInterchange hMom V s hStatus m (p.coeff m : ℝ)
    (fun x => hDegree m hm x) (fun x hx k => hNoOut m hm x hx k)

lemma map_invertPolynomial (I : Finset (Fin 20)) (p : VecPoly) :
    MvPolynomial.map (Rat.castHom ℝ) (invertPolynomial I p) =
      invertRealPolynomial I (MvPolynomial.map (Rat.castHom ℝ) p) := by
  unfold invertPolynomial invertRealPolynomial
  rw [MvPolynomial.eval₂Hom_C_eq_bind₁, MvPolynomial.eval₂Hom_C_eq_bind₁]
  change MvPolynomial.map (Rat.castHom ℝ)
      (MvPolynomial.bind₁ (fun v =>
        (if v.1 ∈ I then -1 else 1) * MvPolynomial.X v) p) =
    MvPolynomial.bind₁ (fun v =>
      (if v.1 ∈ I then -1 else 1) * MvPolynomial.X v)
        (MvPolynomial.map (Rat.castHom ℝ) p)
  rw [MvPolynomial.map_bind₁]
  apply congrArg (fun f : (Fin 20 × Fin 3) → MvPolynomial (Fin 20 × Fin 3) ℝ =>
    MvPolynomial.bind₁ f (MvPolynomial.map (Rat.castHom ℝ) p))
  funext v
  by_cases h : v.1 ∈ I <;> simp [h, MvPolynomial.map_X]

lemma pauliOperator_map (J : Finset (Fin 20)) (p : VecPoly) :
    pauliOperator J p = realPauliOperator J (MvPolynomial.map (Rat.castHom ℝ) p) := by
  classical
  ext σ τ
  simp [pauliOperator, realPauliOperator, MvPolynomial.coeff_map]

lemma realPauliOperator_sum {ι : Type*} [Fintype ι] (J : Finset (Fin 20))
    (p : ι → MvPolynomial (Fin 20 × Fin 3) ℝ) :
    realPauliOperator J (∑ i, p i) = ∑ i, realPauliOperator J (p i) := by
  classical
  ext σ τ
  simp only [Matrix.sum_apply, realPauliOperator, MvPolynomial.coeff_sum,
    Complex.ofReal_sum]
  calc
    (∑ a : J → Fin 4,
        (∑ i : ι, ((p i).coeff (pauliExponent J a) : ℂ)) *
          ∏ j : J, pauli (a j) (σ j) (τ j)) =
      ∑ a : J → Fin 4, ∑ i : ι,
        ((p i).coeff (pauliExponent J a) : ℂ) *
          ∏ j : J, pauli (a j) (σ j) (τ j) := by
            apply Finset.sum_congr rfl
            intro a ha
            exact Finset.sum_mul Finset.univ _ _
    _ = ∑ i : ι, ∑ a : J → Fin 4,
        ((p i).coeff (pauliExponent J a) : ℂ) *
          ∏ j : J, pauli (a j) (σ j) (τ j) := by
            exact Finset.sum_comm (s := (Finset.univ : Finset (J → Fin 4)))
              (t := (Finset.univ : Finset ι))
              (f := fun a i =>
                ((p i).coeff (pauliExponent J a) : ℂ) *
                  ∏ j : J, pauli (a j) (σ j) (τ j))

lemma realPauliOperator_smul (J : Finset (Fin 20)) (r : ℝ)
    (p : MvPolynomial (Fin 20 × Fin 3) ℝ) :
    realPauliOperator J (r • p) = r • realPauliOperator J p := by
  classical
  ext σ τ
  simp only [Matrix.smul_apply, realPauliOperator, MvPolynomial.coeff_smul,
    smul_eq_mul, Complex.ofReal_mul, Complex.real_smul]
  calc
    (∑ a : J → Fin 4,
        ((r : ℂ) * (p.coeff (pauliExponent J a) : ℂ)) *
          ∏ j : J, pauli (a j) (σ j) (τ j)) =
      ∑ a : J → Fin 4,
        (r : ℂ) * ((p.coeff (pauliExponent J a) : ℂ) *
          ∏ j : J, pauli (a j) (σ j) (τ j)) := by
            apply Finset.sum_congr rfl
            intro a ha
            ring
    _ = (r : ℂ) * ∑ a : J → Fin 4,
        (p.coeff (pauliExponent J a) : ℂ) *
          ∏ j : J, pauli (a j) (σ j) (τ j) := by
            symm
            exact Finset.mul_sum Finset.univ _ _

lemma invertRealPolynomial_sum_smul {ι : Type*} [Fintype ι] (I : Finset (Fin 20))
    (r : ι → ℝ) (p : ι → MvPolynomial (Fin 20 × Fin 3) ℝ) :
    invertRealPolynomial I (∑ i, r i • p i) =
      ∑ i, r i • invertRealPolynomial I (p i) := by
  classical
  unfold invertRealPolynomial
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval₂Hom_C]

theorem main : AKLT.Blueprint.H1.MomentPauliInterchangeStatement := by
  classical
  intro hMom V s hStatus p hInt J I
  simp only [rawPauliFunctional]
  rw [pauliOperator_map, map_invertPolynomial]
  rw [contractSpinMap_interchange hMom V s hStatus p hInt]
  rw [invertRealPolynomial_sum_smul, realPauliOperator_sum]
  simp_rw [realPauliOperator_smul]
  ext σ τ
  simp [Matrix.sum_apply, Matrix.smul_apply, Complex.real_smul, Complex.ofReal_prod]

end AKLT.W.H1M051
