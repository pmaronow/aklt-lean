import AKLT.Defs.FrameModel

noncomputable section
open scoped BigOperators

namespace AKLT.Defs
open AKLT.Challenge

/-- `p:toruskernel`: four actual neighbours on the frozen torus, also at period three. -/
def torusNeighbours {L N : Size} (x : Site L N) : Finset (Site L N) :=
  {(x.1 + 1, x.2), (x.1 - 1, x.2), (x.1, x.2 + 1), (x.1, x.2 - 1)}

/-- Convert an ordinary physical polynomial to the frozen orthonormal coordinates. -/
def polynomialState {L N : Size} (p : SpinorPolynomial L N) : Hilbert L N :=
  WithLp.toLp 2 fun σ => p.coeff (monomialDegree σ) /
    ∏ x : Site L N, (Real.sqrt (Nat.choose 4 (σ x).val : ℝ) : ℂ)

/-- `p:toruskernel`: reversing any selected edges changes only the corresponding singlet signs. -/
def reorientedB (L N : Size) (ε : Bond L N → Bool) : Hilbert L N :=
  polynomialState (∏ e : Bond L N, if ε e then singlet e else -singlet e)

/-- `l:star`: the five-site tensor coordinates, using the frozen spin-two matrices. -/
abbrev StarHilbert := EuclideanSpace ℂ (Fin 5 → Fin 5)

/-- A frozen spin matrix lifted to one factor of the five-site star. -/
def starAtSite (A : Matrix (Fin 5) (Fin 5) ℂ) (x : Fin 5) : Module.End ℂ StarHilbert :=
  Matrix.toEuclideanLin fun σ τ => if ∀ y, y ≠ x → σ y = τ y then A (σ x) (τ x) else 0

/-- The frozen Casimir formula on the central factor and leaf j+1. -/
def starCasimir (j : Fin 4) : Module.End ℂ StarHilbert :=
  let y : Fin 5 := ⟨j.val + 1, by omega⟩
  let Z := starAtSite spinZ 0 + starAtSite spinZ y
  let U := starAtSite spinPlus 0 + starAtSite spinPlus y
  let D := starAtSite spinMinus 0 + starAtSite spinMinus y
  Z * Z + (1 / 2 : ℂ) • (U * D + D * U)

/-- `l:star`: the actual sum of four total-spin-four orthogonal projectors. -/
def starHamiltonian : Module.End ℂ StarHilbert :=
  ∑ j : Fin 4, (Module.End.eigenspace (starCasimir j) 20).starProjection.toLinearMap

/-- `l:star`: the smallest positive eigenvalue, whose existence and positivity are stated explicitly. -/
def starGap : ℝ := sInf {μ : ℝ | 0 < μ ∧ starHamiltonian.HasEigenvalue (μ : ℂ)}

/-- `l:star`: H_x uses exactly the incident frozen projectors. -/
def siteHamiltonian {L N : Size} (x : Site L N) : Module.End ℂ (Hilbert L N) :=
  ∑ e : Bond L N, if x ∈ bondSites e then P e else 0

/-- Eventual ground-space and spectral-gap conclusion, with the actual frozen H and B. -/
def EventualMain : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ L₀ : ℕ, 3 ≤ L₀ ∧
    ∀ L N : Size, L₀ ≤ L.val → L₀ ≤ N.val →
      LinearMap.ker (H L N) = Submodule.span ℂ {B L N} ∧
      ∀ μ : ℝ, μ ≠ 0 → (H L N).HasEigenvalue (μ : ℂ) → c ≤ μ

end AKLT.Defs
