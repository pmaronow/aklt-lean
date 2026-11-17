import AKLT.Defs.OperatorContracts

/-! Real-coefficient forms for Appendix D. Rational reconstruction definitions
remain unchanged for the existing certificate proofs. -/

noncomputable section
open scoped BigOperators

namespace AKLT.Defs

/-- `d:Pauli`: arbitrary real polynomials on an arbitrary finite number of vectors. -/
abbrev RealVectorPolynomial (n : ℕ) := MvPolynomial (Fin n × Fin 3) ℝ

/-- `d:Pauli`: separate affineness in each whole vector, with real coefficients. -/
def VectorAffineReal {n : ℕ} (p : RealVectorPolynomial n) : Prop :=
  ∀ m ∈ p.support, ∀ j : Fin n, (∑ k : Fin 3, m (j, k)) ≤ 1

/-- The active tensor tokens include every variable used by the real polynomial. -/
def SupportedVectorsReal {n : ℕ} (J : Finset (Fin n)) (p : RealVectorPolynomial n) : Prop :=
  ∀ m ∈ p.support, ∀ j : Fin n, j ∉ J → ∀ k : Fin 3, m (j, k) = 0

/-- `d:Pauli`: inversion for arbitrary real coefficients and finite vector counts. -/
def invertPolynomialReal {n : ℕ} (I : Finset (Fin n)) (p : RealVectorPolynomial n) :
    RealVectorPolynomial n :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun v =>
    (if v.1 ∈ I then -1 else 1) * MvPolynomial.X v) p

/-- Evaluation of the real polynomial, including irrational constant coefficients. -/
def evaluateRealPolynomial {n : ℕ} (p : RealVectorPolynomial n) (u : Fin n → Vec3) : ℝ :=
  MvPolynomial.eval (fun v => u v.1 v.2) p

/-- Pauli expansion exponent, for any finite active token set. -/
def pauliExponentReal {n : ℕ} (J : Finset (Fin n)) (a : J → Fin 4) : (Fin n × Fin 3) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun v =>
    if h : v.1 ∈ J then if (a ⟨v.1, h⟩).val = v.2.val + 1 then 1 else 0 else 0

/-- `d:Pauli`: the full real-coefficient Pauli operator. -/
def pauliOperatorReal {n : ℕ} (J : Finset (Fin n)) (p : RealVectorPolynomial n) :
    Matrix (J → Fin 2) (J → Fin 2) ℂ :=
  fun σ τ => ∑ a : J → Fin 4,
    (p.coeff (pauliExponentReal J a) : ℂ) * ∏ j : J, pauli (a j) (σ j) (τ j)

/-- Product densities in arbitrary finite tensor coordinates. -/
def productDensityReal {n : ℕ} (J : Finset (Fin n)) (u : Fin n → Vec3) :
    Matrix (J → Fin 2) (J → Fin 2) ℂ :=
  fun σ τ => ∏ j : J, spinDensity (u j.val) (σ j) (τ j)

/-- Vector inversion in arbitrary finite coordinates. -/
def invertVectorsReal {n : ℕ} (I : Finset (Fin n)) (u : Fin n → Vec3) : Fin n → Vec3 :=
  fun j => if j ∈ I then -u j else u j

/-- `d:reduction`: exact rational current/next coefficients embedded in the real ring. -/
def reducedPolynomialReal (π : PatternData) (r : Representation) (next : Bool) : RealVectorPolynomial 20 :=
  MvPolynomial.map (Rat.castHom ℝ) (reducedPolynomial π r next)

/-- `d:reduction`, `c:reduce`, `l:Ostruct`: every real threshold in (0,1).
Only the later integer certificate contract restricts the threshold to rationals. -/
def reducedDifferenceReal (π : PatternData) (r : Representation) (c : ℝ) : RealVectorPolynomial 20 :=
  reducedPolynomialReal π r false - MvPolynomial.C c * reducedPolynomialReal π r true

end AKLT.Defs
