module
public import AKLT.Cert.H1.Production.TopLeaves

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.H1C003

/-- A diagonal substitution preserves each monomial exponent. -/
def scaleVariables {σ : Type*} (s : σ → ℚ) :
    MvPolynomial σ ℚ →+* MvPolynomial σ ℚ :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun v => MvPolynomial.C (s v) * MvPolynomial.X v)

def monomialScale {σ : Type*} (s : σ → ℚ) (d : σ →₀ ℕ) : ℚ :=
  d.prod (fun v n => s v ^ n)

@[simp] theorem scaleVariables_C {σ : Type*} (s : σ → ℚ) (c : ℚ) :
    scaleVariables s (MvPolynomial.C c) = MvPolynomial.C c := by
  simp [scaleVariables]

@[simp] theorem scaleVariables_X {σ : Type*} (s : σ → ℚ) (v : σ) :
    scaleVariables s (MvPolynomial.X v) = MvPolynomial.C (s v) * MvPolynomial.X v := by
  simp [scaleVariables]

theorem scaleVariables_monomial {σ : Type*} (s : σ → ℚ)
    (d : σ →₀ ℕ) (c : ℚ) :
    scaleVariables s (MvPolynomial.monomial d c) =
      MvPolynomial.monomial d (c * monomialScale s d) := by
  classical
  rw [scaleVariables, MvPolynomial.eval₂Hom_monomial, MvPolynomial.monomial_eq]
  have hprod :
      d.prod (fun v n => (MvPolynomial.C (s v) * MvPolynomial.X v) ^ n) =
        MvPolynomial.C (monomialScale s d) *
          d.prod (fun v n => MvPolynomial.X v ^ n) := by
    simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, monomialScale,
      ← map_pow, ← map_prod]
  rw [hprod, ← mul_assoc, ← map_mul]

theorem coeff_scaleVariables {σ : Type*} (s : σ → ℚ)
    (p : MvPolynomial σ ℚ) (d : σ →₀ ℕ) :
    (scaleVariables s p).coeff d = p.coeff d * monomialScale s d := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq =>
      rw [map_add]
      change (scaleVariables s p).coeff d + (scaleVariables s q).coeff d =
        (p.coeff d + q.coeff d) * monomialScale s d
      rw [hp, hq, add_mul]
  | monomial d' c =>
      rw [scaleVariables_monomial, MvPolynomial.coeff_monomial,
        MvPolynomial.coeff_monomial]
      by_cases h : d' = d
      · subst d'
        simp
      · simp [h]

def inversionSign (I : Finset (Fin 20)) (v : Fin 20 × Fin 3) : ℚ :=
  if v.1 ∈ I then -1 else 1

theorem invertPolynomial_eq_scaleVariables (I : Finset (Fin 20))
    (p : MvPolynomial (Fin 20 × Fin 3) ℚ) :
    invertPolynomial I p = scaleVariables (inversionSign I) p := by
  unfold invertPolynomial scaleVariables
  apply MvPolynomial.eval₂Hom_congr rfl _ rfl
  funext v
  by_cases h : v.1 ∈ I <;> simp [inversionSign, h]

/-- Membership in the image of the integers in the rationals. -/
def IntegralRat (x : ℚ) : Prop := ∃ z : ℤ, x = z

theorem integralRat_intCast (z : ℤ) : IntegralRat (z : ℚ) := ⟨z, rfl⟩

theorem IntegralRat.add {x y : ℚ} (hx : IntegralRat x) (hy : IntegralRat y) :
    IntegralRat (x + y) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a + b, (Int.cast_add a b).symm⟩

theorem IntegralRat.sub {x y : ℚ} (hx : IntegralRat x) (hy : IntegralRat y) :
    IntegralRat (x - y) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a - b, (Int.cast_sub a b).symm⟩

theorem IntegralRat.mul {x y : ℚ} (hx : IntegralRat x) (hy : IntegralRat y) :
    IntegralRat (x * y) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a * b, (Int.cast_mul a b).symm⟩

theorem IntegralRat.pow {x : ℚ} (hx : IntegralRat x) (n : ℕ) :
    IntegralRat (x ^ n) := by
  obtain ⟨a, rfl⟩ := hx
  exact ⟨a ^ n, (Int.cast_pow a n).symm⟩

theorem integralRat_sum {ι : Type*} (s : Finset ι) (f : ι → ℚ)
    (h : ∀ i ∈ s, IntegralRat (f i)) : IntegralRat (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using integralRat_intCast 0
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact (h i (Finset.mem_insert_self i s)).add
        (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

theorem integralRat_prod {ι : Type*} (s : Finset ι) (f : ι → ℚ)
    (h : ∀ i ∈ s, IntegralRat (f i)) : IntegralRat (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using integralRat_intCast 1
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi]
      exact (h i (Finset.mem_insert_self i s)).mul
        (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

theorem integralRat_inversionScale (I : Finset (Fin 20))
    (d : (Fin 20 × Fin 3) →₀ ℕ) :
    IntegralRat (monomialScale (inversionSign I) d) := by
  classical
  apply integralRat_prod
  intro v _
  apply IntegralRat.pow
  unfold inversionSign
  split_ifs
  · simpa using integralRat_intCast (-1)
  · simpa using integralRat_intCast 1

theorem denominator_inverted_coeff (π : PatternData) (r : Representation)
    (D₀ : ℕ) (hD : ClearsDenominator π r D₀) (I : Finset (Fin 20))
    (next : Bool) (d : (Fin 20 × Fin 3) →₀ ℕ) :
    IntegralRat ((if next then 5 else 3) * (D₀ : ℚ) *
      (invertPolynomial I (reducedPolynomial π r next)).coeff d) := by
  classical
  rw [invertPolynomial_eq_scaleVariables, coeff_scaleVariables, ← mul_assoc]
  apply IntegralRat.mul _ (integralRat_inversionScale I d)
  by_cases hd : d ∈ (reducedPolynomial π r next).support
  · exact hD.2 next d hd
  · have hz : (reducedPolynomial π r next).coeff d = 0 :=
      MvPolynomial.notMem_support_iff.mp hd
    simpa [hz] using integralRat_intCast 0

end AKLT.W.H1C003
