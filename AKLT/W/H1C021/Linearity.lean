module
public import AKLT.Cert.H1.Production.Leaves

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Cert.H1 AKLT.Cert.H1.Production

namespace AKLT.W.H1C021

theorem rationalOperatorEntry_add (J : Finset (Fin 20))
    (p q : VectorPolynomial) (σ τ : J → Fin 2) :
    rationalOperatorEntry J (p + q) σ τ =
      rationalOperatorEntry J p σ τ + rationalOperatorEntry J q σ τ := by
  classical
  simp [rationalOperatorEntry, Finset.sum_add_distrib, add_mul]

theorem rationalSectorEntry_add (π : PatternData) (r : Representation)
    (ε : ExchangeSigns π) (p q : VectorPolynomial) (a b : CentralBasis π r ε) :
    rationalSectorEntry π r ε (p + q) a b =
      rationalSectorEntry π r ε p a b + rationalSectorEntry π r ε q a b := by
  classical
  unfold rationalSectorEntry
  simp_rw [rationalOperatorEntry_add, mul_add, add_mul]
  simp only [Finset.sum_add_distrib]

theorem rationalSectorEntry_list_sum (π : PatternData) (r : Representation)
    (ε : ExchangeSigns π) (ps : List VectorPolynomial) (a b : CentralBasis π r ε) :
    rationalSectorEntry π r ε ps.sum a b =
      (ps.map fun p => rationalSectorEntry π r ε p a b).sum := by
  induction ps with
  | nil => simp [rationalSectorEntry, rationalOperatorEntry]
  | cons p ps ih => simp [rationalSectorEntry_add, ih]

theorem rationalOperatorEntry_C_mul (J : Finset (Fin 20))
    (k : ℚ) (p : VectorPolynomial) (σ τ : J → Fin 2) :
    rationalOperatorEntry J (MvPolynomial.C k * p) σ τ =
      k * rationalOperatorEntry J p σ τ := by
  classical
  unfold rationalOperatorEntry
  simp only [MvPolynomial.coeff_C_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  ring

theorem rationalSectorEntry_C_mul (π : PatternData) (r : Representation)
    (ε : ExchangeSigns π) (k : ℚ) (p : VectorPolynomial) (a b : CentralBasis π r ε) :
    rationalSectorEntry π r ε (MvPolynomial.C k * p) a b =
      k * rationalSectorEntry π r ε p a b := by
  classical
  unfold rationalSectorEntry
  simp_rw [rationalOperatorEntry_C_mul]
  simp_rw [show ∀ (x y z : ℚ), x * (k * y) * z = k * (x * y * z) by intros; ring]
  simp only [Finset.mul_sum]

theorem sumGaussian_re_cast (xs : List Gaussian) :
    ((sumGaussian xs).re : ℚ) = (xs.map fun z => (z.re : ℚ)).sum := by
  induction xs with
  | nil => simp [sumGaussian, Gaussian.zero]
  | cons x xs ih => simp [sumGaussian, Gaussian.add, ih]

theorem complex_re_list_sum (xs : List ℂ) :
    xs.sum.re = (xs.map Complex.re).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]

end AKLT.W.H1C021
