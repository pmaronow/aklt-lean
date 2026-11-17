module
public import AKLT.Blueprint.Top.Common
public import AKLT.Defs.Quantum
public import AKLT.Defs.Specification

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Challenge

namespace AKLT.Blueprint.Top

/-- `l:threeframes`: exact rotation, moment identity, antipodality, attained bound,
and separation even up to signs. The three weights are uniformly 1/12. -/
def ThreeFramesStatement : Prop :=
  frameRotation.transpose * frameRotation = 1 ∧ frameRotation.det = 1 ∧
  0 < frameBound ∧ frameBound < 1 ∧ 0 < frameRatio ∧ frameRatio < 1 ∧
  (∀ j : Fin 3, Function.Injective (frameVector j) ∧
    (∀ a, normSq (frameVector j a) = 1) ∧ (∀ a, ∃ b, frameVector j b = -frameVector j a) ∧
    ∀ p : MvPolynomial (Fin 3) ℝ, DegreeFour p →
      (1 / 12 : ℝ) * (∑ a : IcoLetter, MvPolynomial.eval (frameVector j a) p) =
        moment (fun a => MvPolynomial.eval a p)) ∧
  (∀ i j : Fin 3, i ≠ j → ∀ a b : IcoLetter,
    frameBound ≤ 1 + dot (frameVector i a) (frameVector j b) ∧
    1 + dot (frameVector i a) (frameVector j b) ≤ 2 - frameBound ∧
    frameBound ≤ 1 - dot (frameVector i a) (frameVector j b) ∧
    1 - dot (frameVector i a) (frameVector j b) ≤ 2 - frameBound ∧
    frameVector i a ≠ frameVector j b ∧ frameVector i a ≠ -frameVector j b) ∧
  ∃ i j : Fin 3, i ≠ j ∧ ∃ a b : IcoLetter,
    1 - dot (frameVector i a) (frameVector j b) = frameBound

/-- `l:tight`: finite coherent-state tight identity for any frame and any compatible
finite spinor choices, plus the actual tensor isometry used for the frozen torus frames. -/
def TightStatement : Prop :=
  (∀ j : Fin 3, ∀ a : IcoLetter,
    (∑ k : Fin 2, Complex.normSq (frameSpinor j a k)) = 1 ∧
      (fun k l => frameSpinor j a k * star (frameSpinor j a l)) = spinDensity (frameVector j a)) ∧
  (∀ n : ℕ, ∀ F : FrameData n, IsFrame F → ∀ ζ : Fin n → Spinor,
    (∀ a, (∑ k, Complex.normSq (ζ a k)) = 1 ∧
      (fun k l => ζ a k * star (ζ a l)) = spinDensity (F.point a)) →
    ∀ p : BinaryForm 4,
      (∑ a, 5 * F.weight a * Complex.normSq (binaryEval 4 p (ζ a))) = binaryNormSq 4 p) ∧
  (∀ L N : Size, ∀ κ : Site L N → Fin 3, ∀ ψ : Hilbert L N,
    (∑ σ, torusReference L N σ * Complex.normSq (frameEval κ ψ σ)) = ‖ψ‖^2) ∧
  ∀ L N : Size, ∀ k : Site L N → ℕ, ∀ F : (x : Site L N) → FrameData (k x),
    (∀ x, IsFrame (F x)) → ∀ ζ : (x : Site L N) → Fin (k x) → Spinor,
    (∀ x a, (∑ i, Complex.normSq (ζ x a i)) = 1 ∧
      (fun i j => ζ x a i * star (ζ x a j)) = spinDensity ((F x).point a)) →
    ∀ ψ : Hilbert L N,
      (∑ σ : (x : Site L N) → Fin (k x), (∏ x, 5 * (F x).weight (σ x)) *
        Complex.normSq (physicalEval ψ (fun x => ζ x (σ x)))) = ‖ψ‖^2

/-- `p:toruskernel`: simple degree-four tori at every size, a nonzero VBS vector,
the exact ground line, and its independence of the selected edge orientations. -/
def TorusKernelStatement : Prop :=
  ∀ L N : Size,
    (∀ e : Bond L N, (bondSites e).card = 2) ∧ Function.Injective (@bondSites L N) ∧
    (∀ x : Site L N, (torusNeighbours x).card = 4 ∧ x ∉ torusNeighbours x) ∧
    B L N ≠ 0 ∧ LinearMap.ker (H L N) = Submodule.span ℂ {B L N} ∧
    ∀ ε : Bond L N → Bool, Submodule.span ℂ {reorientedB L N ε} = Submodule.span ℂ {B L N}

/-- `l:star`: the fixed five-site gap is positive, and the two incident-star comparisons
use the frozen torus projectors, with the exact multiplicity two. -/
def StarStatement : Prop :=
  0 < starGap ∧ starHamiltonian.HasEigenvalue (starGap : ℂ) ∧
  (∀ μ : ℝ, 0 < μ → starHamiltonian.HasEigenvalue (μ : ℂ) → starGap ≤ μ) ∧
  ∀ L N : Size, (∑ x : Site L N, siteHamiltonian x) = 2 • H L N ∧
    ∀ x : Site L N, ∀ ψ : Hilbert L N,
      starGap * ‖ψ - (LinearMap.ker (siteHamiltonian x)).starProjection ψ‖^2 ≤
        (inner ℂ ψ (siteHamiltonian x ψ)).re

/-- `t:QD`: exact squared-modulus density and quantum coercivity for every torus
and proper coloring. Quantification over all Poincare lower bounds is the form version
of the displayed gap inequality and remains meaningful on one-point products. -/
def QDStatement : Prop :=
  ∀ L N : Size, ∀ κ : Site L N → Fin 3, ProperTorusColouring κ →
    (∀ σ, torusLaw L N κ σ =
      torusReference L N σ * Complex.normSq (frameEval κ (B L N) σ) / ‖B L N‖^2) ∧
    ∀ γ : ℝ, PoincareLower (torusLaw L N κ) γ → ∀ ψ : Hilbert L N,
      inner ℂ (B L N) ψ = 0 → (starGap / 2) * γ * ‖ψ‖^2 ≤ (inner ℂ ψ (H L N ψ)).re

/-- `l:planeenergy`: full support and conditioning consistency, uniform partial-fiber
assignment bounds with alpha in (0,1], and the internal-edge-only block Poincare bound. -/
def PlaneEnergyStatement : Prop :=
  0 < frameEnergy ∧ frameEnergy ≤ 1 ∧
  (∀ κ : Plane → Fin 3, ProperPlaneColouring κ → ∀ W : Finset Plane, ∀ η : FrameBoundary W,
    PositiveProbability (planeLaw κ W η) ∧
    (∀ V : Finset Plane, V ⊆ W → ∀ σ : PlaneConfiguration W,
      conditionalPlaneLaw κ W V η σ = planeLaw κ V (inducedBoundary W V η σ)) ∧
    (∀ U J : Finset Plane, U ⊆ W → J ⊆ W → Disjoint U J →
      ∀ a b : Plane → IcoLetter,
      conditionalProbability (planeLaw κ W η)
        (fun σ => ∀ x ∈ J, extendLetters σ x = a x)
        (fun σ => ∀ x ∈ U, extendLetters σ x = b x) ≥ frameEnergy ^ U.card) ∧
    PoincareLower (planeLaw κ W η) (frameRatio ^ (internalBonds W).card)) ∧
  ∀ L N : Size, ∀ κ : Site L N → Fin 3, ProperTorusColouring κ →
    PositiveProbability (torusLaw L N κ) ∧
    (∀ U : Finset (Site L N), ∀ σ ξ : TorusConfiguration L N,
      (∀ z ∈ (U.biUnion torusNeighbours) \ U, σ z = ξ z) →
        conditionalTorusLaw L N κ U σ = conditionalTorusLaw L N κ U ξ) ∧
    ∀ U J : Finset (Site L N), Disjoint U J → ∀ a b : TorusConfiguration L N,
      conditionalProbability (torusLaw L N κ) (fun σ => ∀ x ∈ J, σ x = a x)
        (fun σ => ∀ x ∈ U, σ x = b x) ≥ frameEnergy ^ U.card

end AKLT.Blueprint.Top
