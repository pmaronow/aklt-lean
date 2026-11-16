import AKLT.Blueprint.Q.Definitions

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Challenge

namespace AKLT.Blueprint.Q

/-- `d:poly`, sec3 lines 68–73, and finite spinor choice: verify the explicit
north-chart formula, treating the south pole first. The unit premise makes
both non-pole square-root denominators strictly positive. -/
def SpinorChoiceStatement : Prop :=
  ∀ v : Vec3, normSq v = 1 → compatible v (chosenSpinor v)

/-- `l:tight`, lines 287–298: total degree of each explicit complex kernel.
Use j<=k or k<j before simplifying natural-number exponent differences. -/
def QuarticKernelDegreeStatement : Prop :=
  ∀ j k : Fin 5, (quarticKernel j k).totalDegree ≤ 4

/-- `l:tight`, lines 287–297: pair spinor factors using the density-matrix
entries; use the conjugate formula when j>k. -/
def QuarticKernelEvaluationStatement : Prop :=
  ∀ v : Vec3, ∀ z : Spinor, compatible v z → ∀ j k : Fin 5,
    star (quarticMonomial j z) * quarticMonomial k z =
      MvPolynomial.eval (fun i => (v i : ℂ)) (quarticKernel j k)

/-- `d:frame`, sec3 lines 271–272: complexify any finite real quadrature
by mapping coefficients to real and imaginary parts. No positivity needed. -/
def ComplexQuadratureStatement : Prop :=
  ∀ (A : Type) [Fintype A], ∀ v : A → Vec3, ∀ w : A → ℝ,
    quadrature v w → ∀ p : MvPolynomial (Fin 3) ℂ, p.totalDegree ≤ 4 →
      (∑ a, (w a : ℂ) * MvPolynomial.eval (fun i => (v a i : ℂ)) p) = complexMoment p

/-- `l:tight`, lines 298–302: the off-diagonal kernel averages vanish.
Expand the finite moment sum (or use the finite degree-four rotation
covariance); no integration on the sphere is involved. -/
def QuarticOffDiagonalStatement : Prop :=
  ∀ j k : Fin 5, j ≠ k → complexMoment (quarticKernel j k) = 0

/-- `l:tight`, lines 304–318: the five diagonal averages, with the exact
inverse-binomial normalization. A fixed five-case radical calculation. -/
def QuarticDiagonalStatement : Prop :=
  ∀ j : Fin 5, 5 * complexMoment (quarticKernel j j) = (Nat.choose 4 j.val : ℂ)⁻¹

/-- `l:tight`, lines 319–326: expand a linear combination in an already
resolved monomial Gram matrix. This is a generic finite-sum algebra step. -/
def ResolutionExpansionStatement : Prop :=
  ∀ (A : Type) [Fintype A], ∀ w : A → ℝ, ∀ z : A → Spinor,
    resolution w z → ∀ p : BinaryForm 4,
      (∑ a, 5 * w a * Complex.normSq (binaryEval 4 p (z a))) = binaryNormSq 4 p

/-- `l:tight`, lines 328–333: finite tensorization of the five-by-five
local Gram identities, then orthonormal-coordinate binomial cancellation.
Dependent alphabets are retained; no equality of alphabet cardinalities is assumed. -/
def TensorResolutionStatement : Prop :=
  ∀ L N : Size, ∀ S : Site L N → Type, ∀ (_ : ∀ x, Fintype (S x)),
    ∀ w : (x : Site L N) → S x → ℝ, ∀ z : (x : Site L N) → S x → Spinor,
      (∀ x, resolution (w x) (z x)) → ∀ ψ : Hilbert L N,
        (∑ σ : (x : Site L N) → S x, (∏ x, 5 * w x (σ x)) *
          Complex.normSq (physicalEval ψ (fun x => z x (σ x)))) = ‖ψ‖^2

end AKLT.Blueprint.Q
