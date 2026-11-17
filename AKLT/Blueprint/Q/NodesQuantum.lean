module
public import AKLT.Blueprint.Q.Definitions

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Challenge

namespace AKLT.Blueprint.Q

/-- `l:qmod`, sec3 lines 458–485: expand the determinant and the four density
matrix entries. The normalized-spinor premises and conjugation are explicit. -/
def DeterminantModulusStatement : Prop :=
  ∀ a b : Vec3, ∀ z w : Spinor, compatible a z → compatible b w →
    Complex.normSq (determinant z w) = (1 - dot a b) / 2

/-- `e:frame-ground-weight`, sec3 lines 583–588: multiply the bond modulus
identities. Keep the exact factors 5^|sites| and 2^(-|bonds|). -/
def GroundProductWeightStatement : Prop :=
  ∀ L N : Size, ∀ κ : Site L N → Fin 3,
    (∀ σ, frameEval κ (B L N) σ = ∏ e : Bond L N,
      determinant (frameSpinor (κ e.1) (σ e.1))
        (frameSpinor (κ (nextSite e.1 e.2)) (σ (nextSite e.1 e.2)))) →
    (∀ e : Bond L N, ∀ σ : TorusConfiguration L N,
      Complex.normSq (determinant (frameSpinor (κ e.1) (σ e.1))
        (frameSpinor (κ (nextSite e.1 e.2)) (σ (nextSite e.1 e.2)))) =
      (1 - dot (frameVector (κ e.1) (σ e.1))
        (frameVector (κ (nextSite e.1 e.2)) (σ (nextSite e.1 e.2)))) / 2) →
    ∀ σ, torusReference L N σ * Complex.normSq (frameEval κ (B L N) σ) =
      groundScale L N * torusWeight L N κ σ

/-- `l:quantumfibre`, sec3 lines 570–579: evaluate a polynomial divisible by
the four incident determinants, including their center orientation signs.
The residual polynomial has its own degrees; no residual isometry is assumed. -/
def IncidentEvaluationStatement : Prop :=
  ∀ L N : Size, ∀ κ : Site L N → Fin 3, ∀ x : Site L N,
    ∀ ψ : Hilbert L N, ∀ χ : SpinorPolynomial L N,
      statePolynomial ψ = incidentProduct x * χ → independentAt x χ →
      (∀ σ, frameEval κ ψ σ = centerSign x * beta κ x σ *
        MvPolynomial.eval (fun v => frameSpinor (κ v.1) (σ v.1) v.2) χ) ∧
      inFiberSpan κ x (frameEval κ ψ)

/-- `l:quantumfibre`, lines 570–579: separate the incident factors of B and
show rho is constant on each center fiber. The actual evaluation/product
identity is supplied explicitly, without a second definition of B. -/
def GroundFiberFactorizationStatement : Prop :=
  ∀ L N : Size, ∀ κ : Site L N → Fin 3,
    (∀ σ, frameEval κ (B L N) σ = ∏ e : Bond L N,
      determinant (frameSpinor (κ e.1) (σ e.1))
        (frameSpinor (κ (nextSite e.1 e.2)) (σ (nextSite e.1 e.2)))) →
    ∀ x : Site L N,
      (∀ σ, frameEval κ (B L N) σ = beta κ x σ * rho κ x σ) ∧
      ∀ σ a, rho κ x (Function.update σ x a) = rho κ x σ

/-- `l:quantumfibre`, sec3 lines 595–598: a strictly positive squared-modulus
density gives a unitary multiplication map with its explicit inverse.
The result is stated as finite weighted norm and inverse identities. -/
def GroundTransformStatement : Prop :=
  ∀ L N : Size, ∀ κ : Site L N → Fin 3, B L N ≠ 0 →
    (∀ σ, frameEval κ (B L N) σ ≠ 0) →
    (∀ σ, torusLaw L N κ σ = torusReference L N σ *
      Complex.normSq (frameEval κ (B L N) σ) / ‖B L N‖^2) →
    (∀ f, weightedNorm (torusReference L N) (groundTransform κ f) =
      weightedNorm (torusLaw L N κ) f) ∧
    (∀ ψ, groundTransform κ (groundQuotient κ ψ) = frameEval κ ψ) ∧
    ∀ f σ, (‖B L N‖ : ℂ) * groundTransform κ f σ / frameEval κ (B L N) σ = f σ

/-- `l:quantumfibre`, sec3 lines 600–623: compare the two finite fiber
quotients. Include the integrated residual identity needed by t:QD.
Positive beta makes every displayed fiber denominator positive. -/
def FiberIntertwiningStatement : Prop :=
  ∀ L N : Size, ∀ κ : Site L N → Fin 3, ∀ x : Site L N, B L N ≠ 0 →
    (∀ σ, beta κ x σ ≠ 0) →
    (∀ σ, frameEval κ (B L N) σ = beta κ x σ * rho κ x σ) →
    (∀ σ a, rho κ x (Function.update σ x a) = rho κ x σ) →
    (∀ σ, torusLaw L N κ σ = torusReference L N σ *
      Complex.normSq (frameEval κ (B L N) σ) / ‖B L N‖^2) →
    (∀ σ, frameEval κ (B L N) σ ≠ 0) →
    (∀ f, groundTransform κ (conditionalExpectation (torusLaw L N κ) {x} f) =
      fiberProjection κ x (groundTransform κ f)) ∧
    ∀ f, blockDirichlet (torusLaw L N κ) {x} f =
      weightedNorm (torusReference L N)
        (groundTransform κ f - fiberProjection κ x (groundTransform κ f))

/-- `l:quantumfibre`, sec3 lines 609–620, 634–643: the explicit fiber formula
is the orthogonal projection onto beta. Prove positivity of the denominator,
then the finite weighted least-squares identity. Its best-approximation form
is exactly what is needed for the physical-space inclusion argument. -/
def FiberProjectionStatement : Prop :=
  ∀ L N : Size, ∀ κ : Site L N → Fin 3, ∀ x : Site L N,
    (∀ σ, beta κ x σ ≠ 0) →
    (∀ σ, 0 < fiberDenominator κ x σ) ∧
    (∀ h, inFiberSpan κ x (fiberProjection κ x h)) ∧
    (∀ h, inFiberSpan κ x h → fiberProjection κ x h = h) ∧
    ∀ h k, inFiberSpan κ x k →
      weightedNorm (torusReference L N) (h - fiberProjection κ x h) ≤
        weightedNorm (torusReference L N) (h - k)

/-- `t:QD`, sec3 lines 660–667: polarization of a linear weighted norm
isometry. Weights are real; norm equality itself forces the positive form
on the image, so no unmentioned probability normalization is needed. -/
def WeightedPolarizationStatement : Prop :=
  ∀ (ι Ω : Type) [Fintype ι] [Fintype Ω], ∀ w : Weight Ω,
    ∀ E : EuclideanSpace ℂ ι →ₗ[ℂ] (Ω → ℂ),
      (∀ ψ, weightedNorm w (E ψ) = ‖ψ‖^2) →
      ∀ ψ φ, weightedInner w (E ψ) (E φ) = inner ℂ ψ φ

/-- `t:QD`, sec3 lines 664–667: explicit quotient has mean zero and variance
||psi||^2. Use the probability identity, nowhere-zero ground evaluation,
and the supplied inner-product isometry, with conjugation in the first slot. -/
def GroundQuotientVarianceStatement : Prop :=
  ∀ L N : Size, ∀ κ : Site L N → Fin 3, B L N ≠ 0 →
    (∀ σ, frameEval κ (B L N) σ ≠ 0) →
    (∀ σ, torusLaw L N κ σ = torusReference L N σ *
      Complex.normSq (frameEval κ (B L N) σ) / ‖B L N‖^2) →
    (∀ ψ φ, weightedInner (torusReference L N) (frameEval κ ψ) (frameEval κ φ) =
      inner ℂ ψ φ) →
    ∀ ψ : Hilbert L N, inner ℂ (B L N) ψ = 0 →
      complexMean (torusLaw L N κ) (groundQuotient κ ψ) = 0 ∧
      variance (torusLaw L N κ) (groundQuotient κ ψ) = ‖ψ‖^2

/-- `l:quantumfibre`, sec3 lines 541–544, 595, 609: every beta is nonzero
once every incident determinant has strictly positive squared modulus.
The four-neighbor and orientation identifications are part of this finite
product bridge, not an assumed nonvanishing of B. -/
def BetaNonzeroStatement : Prop :=
  ∀ L N : Size, ∀ κ : Site L N → Fin 3,
    (∀ e : Bond L N, ∀ σ : TorusConfiguration L N,
      0 < Complex.normSq (determinant (frameSpinor (κ e.1) (σ e.1))
        (frameSpinor (κ (nextSite e.1 e.2)) (σ (nextSite e.1 e.2))))) →
    ∀ x σ, beta κ x σ ≠ 0

end AKLT.Blueprint.Q
