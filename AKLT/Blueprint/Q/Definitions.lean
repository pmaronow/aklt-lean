module
public import AKLT.Blueprint.Top.Quantum

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

/-! Concrete objects used by the Q blueprint. These are definitions, with no
mathematical facts or typeclass assumptions built into the data. -/

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Challenge

namespace AKLT.Blueprint.Q

def compatible (a : Vec3) (z : Spinor) : Prop :=
  (∑ k, Complex.normSq (z k)) = 1 ∧
    (fun k l => z k * star (z l)) = spinDensity a

def chosenSpinor (v : Vec3) : Spinor :=
  if v 2 = -1 then ![0, 1] else
    ![(Real.sqrt ((1 + v 2) / 2) : ℂ),
      ((v 0 : ℂ) + Complex.I * (v 1 : ℂ)) / (Real.sqrt (2 * (1 + v 2)) : ℂ)]

def determinant (z w : Spinor) : ℂ := z 0 * w 1 - z 1 * w 0

def quarticMonomial (j : Fin 5) (z : Spinor) : ℂ := z 0 ^ (4 - j.val) * z 1 ^ j.val

def quarticKernel (j k : Fin 5) : MvPolynomial (Fin 3) ℂ :=
  let X := fun i : Fin 3 => MvPolynomial.X i
  if j ≤ k then
    MvPolynomial.C (1 / 16 : ℂ) * (1 + X 2) ^ (4 - k.val) *
      (1 - X 2) ^ j.val * (X 0 + MvPolynomial.C Complex.I * X 1) ^ (k.val - j.val)
  else
    MvPolynomial.C (1 / 16 : ℂ) * (1 + X 2) ^ (4 - j.val) *
      (1 - X 2) ^ k.val * (X 0 - MvPolynomial.C Complex.I * X 1) ^ (j.val - k.val)

def complexMoment (p : MvPolynomial (Fin 3) ℂ) : ℂ :=
  (1 / 12 : ℂ) * ∑ a : IcoLetter, MvPolynomial.eval (fun i => (icoVector a i : ℂ)) p

def quadrature {A : Type*} [Fintype A] (v : A → Vec3) (w : A → ℝ) : Prop :=
  ∀ p : MvPolynomial (Fin 3) ℝ, DegreeFour p →
    (∑ a, w a * MvPolynomial.eval (v a) p) = moment (fun u => MvPolynomial.eval u p)

/-- Numerical interaction bounds supplied by the three-frame assembly.
This ordinary data property lets finite-probability leaves avoid repeating
the geometric separation calculation. It asserts no moment identity. -/
def interactionBounds : Prop :=
  ∀ i j : Fin 3, i ≠ j → ∀ a b : IcoLetter,
    frameBound ≤ 1 + dot (frameVector i a) (frameVector j b) ∧
    1 + dot (frameVector i a) (frameVector j b) ≤ 2 - frameBound ∧
    frameBound ≤ 1 - dot (frameVector i a) (frameVector j b) ∧
    1 - dot (frameVector i a) (frameVector j b) ≤ 2 - frameBound

def resolution {A : Type*} [Fintype A] (w : A → ℝ) (z : A → Spinor) : Prop :=
  ∀ j k : Fin 5,
    (∑ a, (5 * w a : ℂ) * star (quarticMonomial j (z a)) * quarticMonomial k (z a)) =
      if j = k then (Nat.choose 4 j.val : ℂ)⁻¹ else 0

def weightedNorm {A : Type*} [Fintype A] (w : Weight A) (f : A → ℂ) : ℝ :=
  ∑ a, w a * Complex.normSq (f a)

def weightedInner {A : Type*} [Fintype A] (w : Weight A) (f g : A → ℂ) : ℂ :=
  ∑ a, (w a : ℂ) * star (f a) * g a

def coherentMap {L N : Size} (κ : Site L N → Fin 3) :
    Hilbert L N →ₗ[ℂ] (TorusConfiguration L N → ℂ) where
  toFun := frameEval κ
  map_add' v w := by
    funext σ
    simp [frameEval, physicalEval, add_mul, Finset.sum_add_distrib]
  map_smul' c v := by
    funext σ
    simp [frameEval, physicalEval, Finset.mul_sum, mul_assoc]

def statePolynomial {L N : Size} (ψ : Hilbert L N) : SpinorPolynomial L N :=
  ∑ σ : Configuration L N,
    MvPolynomial.C (ψ σ * ∏ x, (Real.sqrt (Nat.choose 4 (σ x).val : ℝ) : ℂ)) *
      MvPolynomial.monomial (monomialDegree σ) 1

def siteHomogeneous {L N : Size} (p : SpinorPolynomial L N) (d : Site L N → ℕ) : Prop :=
  ∀ m ∈ p.support, ∀ x, m (x, 0) + m (x, 1) = d x

def independentAt {L N : Size} (x : Site L N) (p : SpinorPolynomial L N) : Prop :=
  ∀ m ∈ p.support, m (x, 0) = 0 ∧ m (x, 1) = 0

def incidentProduct {L N : Size} (x : Site L N) : SpinorPolynomial L N :=
  ∏ e : Bond L N, if x ∈ bondSites e then singlet e else 1

abbrev PairHilbert := EuclideanSpace ℂ (Fin 5 × Fin 5)
abbrev PairPolynomial := MvPolynomial (Fin 2 × Fin 2) ℂ

def pairAt (A : Matrix (Fin 5) (Fin 5) ℂ) (side : Fin 2) : Module.End ℂ PairHilbert :=
  Matrix.toEuclideanLin fun σ τ =>
    if side = 0 then (if σ.2 = τ.2 then A σ.1 τ.1 else 0)
    else (if σ.1 = τ.1 then A σ.2 τ.2 else 0)

def pairCasimir : Module.End ℂ PairHilbert :=
  let Z := pairAt spinZ 0 + pairAt spinZ 1
  let U := pairAt spinPlus 0 + pairAt spinPlus 1
  let D := pairAt spinMinus 0 + pairAt spinMinus 1
  Z * Z + (1 / 2 : ℂ) • (U * D + D * U)

def pairPolynomial (ψ : PairHilbert) : PairPolynomial :=
  ∑ j : Fin 5, ∑ k : Fin 5,
    MvPolynomial.C (ψ (j, k) * (Real.sqrt (Nat.choose 4 j.val : ℝ) : ℂ) *
      (Real.sqrt (Nat.choose 4 k.val : ℝ) : ℂ)) *
    MvPolynomial.X (0, 0) ^ (4 - j.val) * MvPolynomial.X (0, 1) ^ j.val *
    MvPolynomial.X (1, 0) ^ (4 - k.val) * MvPolynomial.X (1, 1) ^ k.val

def pairDiagonal : PairHilbert →ₗ[ℂ] MvPolynomial (Fin 2) ℂ where
  toFun ψ := MvPolynomial.rename Prod.snd (pairPolynomial ψ)
  map_add' v w := by
    simp [pairPolynomial, add_mul, Finset.sum_add_distrib]
  map_smul' c v := by
    simp [pairPolynomial, MvPolynomial.smul_eq_C_mul, mul_assoc, Finset.mul_sum]

def pairSinglet : PairPolynomial :=
  MvPolynomial.X (0, 0) * MvPolynomial.X (1, 1) -
    MvPolynomial.X (0, 1) * MvPolynomial.X (1, 0)

def pairProjector : Module.End ℂ PairHilbert :=
  (Module.End.eigenspace pairCasimir 20).starProjection.toLinearMap

def kernelCoercivity {ι : Type*} [Fintype ι]
    (T : Module.End ℂ (EuclideanSpace ℂ ι)) (g : ℝ) : Prop :=
  ∀ ψ, g * ‖ψ - (LinearMap.ker T).starProjection ψ‖^2 ≤ (inner ℂ ψ (T ψ)).re

def amplifiesStar {ι : Type*} [Fintype ι]
    (T : Module.End ℂ (EuclideanSpace ℂ ι)) (n : ℕ)
    (U : EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n × (Fin 5 → Fin 5))) : Prop :=
  ∀ ψ r s, U (T ψ) (r, s) =
    starHamiltonian (WithLp.toLp 2 (fun t => U ψ (r, t))) s

def edgeSign {L N : Size} (x : Site L N) (e : Bond L N) : ℂ :=
  if e.1 = x then 1 else -1

def centreSign {L N : Size} (x : Site L N) : ℂ :=
  ∏ e : Bond L N, if x ∈ bondSites e then edgeSign x e else 1

def beta {L N : Size} (κ : Site L N → Fin 3) (x : Site L N)
    (σ : TorusConfiguration L N) : ℂ :=
  ∏ y ∈ torusNeighbours x, determinant (frameSpinor (κ x) (σ x)) (frameSpinor (κ y) (σ y))

def rho {L N : Size} (κ : Site L N → Fin 3) (x : Site L N)
    (σ : TorusConfiguration L N) : ℂ :=
  centreSign x * ∏ e : Bond L N, if x ∈ bondSites e then 1 else
    determinant (frameSpinor (κ e.1) (σ e.1))
      (frameSpinor (κ (nextSite e.1 e.2)) (σ (nextSite e.1 e.2)))

def inFibreSpan {L N : Size} (κ : Site L N → Fin 3) (x : Site L N)
    (h : TorusConfiguration L N → ℂ) : Prop :=
  ∀ σ, ∃ c : ℂ, ∀ a : IcoLetter,
    h (Function.update σ x a) = c * beta κ x (Function.update σ x a)

def fibreDenominator {L N : Size} (κ : Site L N → Fin 3) (x : Site L N)
    (σ : TorusConfiguration L N) : ℝ :=
  ∑ a : IcoLetter, (5 / 12 : ℝ) * Complex.normSq (beta κ x (Function.update σ x a))

def fibreProjection {L N : Size} (κ : Site L N → Fin 3) (x : Site L N)
    (h : TorusConfiguration L N → ℂ) (σ : TorusConfiguration L N) : ℂ :=
  beta κ x σ *
    (∑ a : IcoLetter, (5 / 12 : ℂ) * star (beta κ x (Function.update σ x a)) *
      h (Function.update σ x a)) / (fibreDenominator κ x σ : ℂ)

def groundScale (L N : Size) : ℝ := 5 ^ Fintype.card (Site L N) / 2 ^ Fintype.card (Bond L N)

def groundTransform {L N : Size} (κ : Site L N → Fin 3)
    (f : TorusConfiguration L N → ℂ) (σ : TorusConfiguration L N) : ℂ :=
  f σ * frameEval κ (B L N) σ / (‖B L N‖ : ℂ)

def groundQuotient {L N : Size} (κ : Site L N → Fin 3)
    (ψ : Hilbert L N) (σ : TorusConfiguration L N) : ℂ :=
  (‖B L N‖ : ℂ) * frameEval κ ψ σ / frameEval κ (B L N) σ

def planeSiteWeight (κ : Plane → Fin 3) (W : Finset Plane) (η : FrameBoundary W)
    (x : W) (a : IcoLetter) : ℝ :=
  (1 / 12 : ℝ) * ∏ e ∈ (originalLegs W).filter (fun e => e.1 = x.val),
    (1 + dot (frameVector (κ x.val) a) (frameVector (κ e.2) (extendBoundary η e.2)))

def planeProductReference (κ : Plane → Fin 3) (W : Finset Plane) (η : FrameBoundary W)
    (σ : PlaneConfiguration W) : ℝ :=
  ∏ x : W, normalize (planeSiteWeight κ W η x) (σ x)

def planeInteraction (κ : Plane → Fin 3) (W : Finset Plane) (σ : PlaneConfiguration W) : ℝ :=
  ∏ e ∈ internalBonds W,
    (1 + dot (frameVector (κ e.1) (extendLetters σ e.1))
      (frameVector (κ e.2) (extendLetters σ e.2)))

def planeInteractionMean (κ : Plane → Fin 3) (W : Finset Plane) (η : FrameBoundary W) : ℝ :=
  ∑ σ, planeProductReference κ W η σ * planeInteraction κ W σ

def planeDensityLower (κ : Plane → Fin 3) (W : Finset Plane) (η : FrameBoundary W) : ℝ :=
  frameBound ^ (internalBonds W).card / planeInteractionMean κ W η

def planeDensityUpper (κ : Plane → Fin 3) (W : Finset Plane) (η : FrameBoundary W) : ℝ :=
  (2 - frameBound) ^ (internalBonds W).card / planeInteractionMean κ W η

def fullFibreEvent {ι : Type*} [DecidableEq ι] {S : ι → Type*}
    (x : ι) (σ τ : (x : ι) → S x) : Prop := ∀ y, y ≠ x → τ y = σ y

end AKLT.Blueprint.Q
