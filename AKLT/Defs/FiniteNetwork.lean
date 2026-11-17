module
public import AKLT.Defs.Probability
public import AKLT.Defs.Operator

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators

namespace AKLT.Defs

/-- `l:finitefacts`: arbitrary finite active spin networks, including covered local templates. -/
structure FiniteSpinNetwork (n : ℕ) where
  status : Fin n → Status
  bonds : Finset (Fin n × Fin n)
  pinCount : Fin n → ℕ
  pin : (x : Fin n) → Fin (pinCount x) → UnitVector

/-- Exactly the degree and distinct-endpoint conditions used in finite positivity. -/
def FiniteSpinNetwork.Valid {n : ℕ} (D : FiniteSpinNetwork n) : Prop :=
  (∀ x, D.status x = .U ∨ D.status x = .D) ∧
  (∀ e ∈ D.bonds, e.1 < e.2) ∧
  ∀ x, (D.bonds.filter fun e => e.1 = x ∨ e.2 = x).card + D.pinCount x ≤ 4

/-- The finite unnormalized weight, with every specified pin factor. -/
def FiniteSpinNetwork.weight {n : ℕ} (D : FiniteSpinNetwork n) (pinned : Bool)
    (σ : Fin n → SpinLetter) : ℝ :=
  (∏ x, spinWeight (D.status x) (σ x)) *
  (∏ e ∈ D.bonds, (1 + dot (spinVector (σ e.1)) (spinVector (σ e.2)))) *
  ∏ x, ∏ j : Fin (D.pinCount x),
    if pinned then 1 + dot (D.pin x j).val (spinVector (σ x)) else 1

/-- Generic finite partition functional. -/
def FiniteSpinNetwork.partition {n : ℕ} (D : FiniteSpinNetwork n) (pinned : Bool)
    (f : (Fin n → Vec3) → ℝ) : ℝ :=
  ∑ σ, D.weight pinned σ * f (fun x => spinVector (σ x))

/-- Conditional probability of an event given a positive-probability event. -/
def conditionalProbability {Ω : Type*} [Fintype Ω] (p : Weight Ω)
    (E A : Ω → Prop) : ℝ := by
  classical
  exact (∑ σ, if E σ ∧ A σ then p σ else 0) / ∑ σ, if E σ then p σ else 0

/-- Conditioning weights, without pretending that a zero-probability fiber is defined probabilistically. -/
def conditionOn {Ω : Type*} [Fintype Ω] (p : Weight Ω) (E : Ω → Prop) : Weight Ω := by
  classical
  exact normalize fun σ => if E σ then p σ else 0

/-- Finite event mass, independent of any measure-theory interface. -/
def eventMass {Ω : Type*} [Fintype Ω] (p : Weight Ω) (E : Ω → Prop) : ℝ := by
  classical
  exact ∑ σ, if E σ then p σ else 0

/-- `l:35`: finite one-site product and normalized vector mean. -/
def localProduct {k : ℕ} (a : Fin k → Vec3) (n : Vec3) : ℝ :=
  ∏ j, (1 + dot n (a j))

def localMean {k : ℕ} (s : Status) (a : Fin k → Vec3) : Vec3 :=
  fun i => siteFunctional s (fun n => n i * localProduct a n) / siteFunctional s (localProduct a)

/-- Complex and rational polynomial evaluations used in the operator interfaces. -/
def evaluateReduced (p : MvPolynomial (Fin 20 × Fin 3) ℚ) (u : Fin 20 → Vec3) : ℝ :=
  MvPolynomial.eval₂ (Rat.castHom ℝ) (fun v => u v.1 v.2) p

/-- `d:Pauli`: product density in the same finite tensor coordinates as the operator. -/
def productDensity (J : Finset (Fin 20)) (u : Fin 20 → Vec3) :
    Matrix (J → Fin 2) (J → Fin 2) ℂ :=
  fun σ τ => ∏ j : J, spinDensity (u j.val) (σ j) (τ j)

/-- `d:Pauli`: inversion on vector data, exactly matching `invertPolynomial`. -/
def invertVectors (I : Finset (Fin 20)) (u : Fin 20 → Vec3) : Fin 20 → Vec3 :=
  fun j => if j ∈ I then -u j else u j

/-- Positivity on a subspace, expressed by its actual ambient Hilbert quadratic form. -/
def PositiveOn {ι : Type*} [Fintype ι] (S : Submodule ℂ (EuclideanSpace ℂ ι))
    (O : Module.End ℂ (EuclideanSpace ℂ ι)) : Prop :=
  ∀ ψ ∈ S, ψ ≠ 0 → 0 < (inner ℂ ψ (O ψ)).re

/-- Eigenvalue set on an invariant subspace; avoids changing inner products in integer coordinates. -/
def eigenvaluesOn {ι : Type*} [Fintype ι] (S : Submodule ℂ (EuclideanSpace ℂ ι))
    (O : Module.End ℂ (EuclideanSpace ℂ ι)) : Set ℂ :=
  {μ | ∃ ψ ∈ S, ψ ≠ 0 ∧ O ψ = μ • ψ}

/-- `d:exchange`: supported sector as an ambient subspace with its inherited Hilbert norm. -/
def exchangeSpace (π : PatternData) (r : Representation) (ε : ExchangeSigns π) :
    Submodule ℂ (EuclideanSpace ℂ (reductionVectors π r → Fin 2)) :=
  Submodule.span ℂ (Set.range fun b : ExchangeBasis π r ε =>
    WithLp.toLp 2 (fun σ => (exchangeBasisVector π r ε b σ : ℂ)))

/-- `d:Pauli`: a one-token matrix lifted to the entire tensor-coordinate space. -/
def tokenMatrix (J : Finset (Fin 20)) (j : J) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (J → Fin 2) (J → Fin 2) ℂ :=
  fun σ τ => if ∀ k, k ≠ j → σ k = τ k then A (σ j) (τ j) else 0

/-- `d:Pauli`: the three ladder operators in actual tensor coordinates. -/
def totalSpinZ (J : Finset (Fin 20)) : Module.End ℂ (EuclideanSpace ℂ (J → Fin 2)) :=
  Matrix.toEuclideanLin ((1 / 2 : ℂ) • ∑ j : J, tokenMatrix J j (pauli 3))

def totalSpinPlus (J : Finset (Fin 20)) : Module.End ℂ (EuclideanSpace ℂ (J → Fin 2)) :=
  Matrix.toEuclideanLin ((1 / 2 : ℂ) • ∑ j : J, tokenMatrix J j (pauli 1 + Complex.I • pauli 2))

def totalSpinMinus (J : Finset (Fin 20)) : Module.End ℂ (EuclideanSpace ℂ (J → Fin 2)) :=
  Matrix.toEuclideanLin ((1 / 2 : ℂ) • ∑ j : J, tokenMatrix J j (pauli 1 - Complex.I • pauli 2))

/-- `d:exchange`: intersection with the actual central weight eigenspace. -/
def centralSpace (π : PatternData) (r : Representation) (ε : ExchangeSigns π) :
    Submodule ℂ (EuclideanSpace ℂ (reductionVectors π r → Fin 2)) :=
  exchangeSpace π r ε ⊓ Module.End.eigenspace (totalSpinZ (reductionVectors π r)) (centralWeight π r : ℂ)

end AKLT.Defs
