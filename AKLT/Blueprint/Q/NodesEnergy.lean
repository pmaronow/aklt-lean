module
public import AKLT.Blueprint.Q.Definitions

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Challenge

namespace AKLT.Blueprint.Q

/-- `d:framemodel`, sec3 lines 519–524: every finite plane and torus weight
is strictly positive. Proper colouring is essential for both signs. -/
def FrameWeightsPositiveStatement : Prop :=
  interactionBounds →
  (∀ κ : Plane → Fin 3, ProperPlaneColouring κ → ∀ W : Finset Plane,
    ∀ η : FrameBoundary W, ∀ σ, 0 < planeWeight κ W η σ) ∧
  ∀ L N : Size, ∀ κ : Site L N → Fin 3, ProperTorusColouring κ →
    ∀ σ, 0 < torusWeight L N κ σ

/-- `d:framemodel`, lines 521–524: positive weights on a nonempty finite
space have a positive normalizer and normalize to a positive probability. -/
def PositiveNormalizationStatement : Prop :=
  ∀ (Ω : Type) [Fintype Ω] [Nonempty Ω], ∀ w : Weight Ω,
    (∀ σ, 0 < w σ) → PositiveProbability (normalize w)

/-- `l:planeenergy`, sec3 lines 709–719: cancel fixed factors on each fibre,
then push forward to the actual smaller configuration space. Empty V and W
are included; V⊆W is needed for the induced boundary identification. -/
def PlaneConditioningStatement : Prop :=
  interactionBounds →
  ∀ κ : Plane → Fin 3, ProperPlaneColouring κ → ∀ W : Finset Plane,
    ∀ η : FrameBoundary W, ∀ V : Finset Plane, V ⊆ W → ∀ σ : PlaneConfiguration W,
      conditionalPlaneLaw κ W V η σ = planeLaw κ V (inducedBoundary W V η σ)

/-- `l:planeenergy`, lines 709–719: only exterior nearest neighbours affect
a torus conditional block law. Crossings are counted once by frozen bonds. -/
def TorusMarkovStatement : Prop :=
  interactionBounds →
  ∀ L N : Size, ∀ κ : Site L N → Fin 3, ProperTorusColouring κ →
    ∀ U : Finset (Site L N), ∀ σ ξ : TorusConfiguration L N,
      (∀ z ∈ (U.biUnion torusNeighbours) \ U, σ z = ξ z) →
        conditionalTorusLaw L N κ U σ = conditionalTorusLaw L N κ U ξ

/-- `l:planeenergy`, lines 721–730: in a fully fixed plane one-site fibre,
at most four factors lie between b and 2-b. Bound numerator and denominator
separately to get (1/12)r_b^4 for each of the twelve letters. -/
def PlaneOneSiteEnergyStatement : Prop :=
  interactionBounds →
  ∀ κ : Plane → Fin 3, ProperPlaneColouring κ → ∀ W : Finset Plane,
    ∀ η : FrameBoundary W, ∀ x : W, ∀ σ : PlaneConfiguration W, ∀ a : IcoLetter,
      frameEnergy ≤ conditionalProbability (planeLaw κ W η) (fullFibreEvent x σ) (fun τ => τ x = a)

/-- `l:planeenergy`, lines 721–730: the same fibre ratio for the all-parity
antiferromagnetic torus; its four incident factors use the minus sign. -/
def TorusOneSiteEnergyStatement : Prop :=
  interactionBounds →
  ∀ L N : Size, ∀ κ : Site L N → Fin 3, ProperTorusColouring κ →
    ∀ x : Site L N, ∀ σ : TorusConfiguration L N, ∀ a : IcoLetter,
      frameEnergy ≤ conditionalProbability (torusLaw L N κ) (fullFibreEvent x σ) (fun τ => τ x = a)

/-- `l:planeenergy`, lines 732–745: average fully fixed fibres, then use a
chain rule on a finite set of distinct sites. Positivity of every intermediate
event follows from full support. Nonempty alphabets and alpha>0 are explicit. -/
def PartialAssignmentStatement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι], ∀ S : ι → Type,
    ∀ (_ : ∀ x, Fintype (S x)) (_ : ∀ x, Nonempty (S x)),
    ∀ p : Weight ((x : ι) → S x), PositiveProbability p → ∀ α : ℝ, 0 < α → α ≤ 1 →
      (∀ x σ a, α ≤ conditionalProbability p (fullFibreEvent x σ) (fun τ => τ x = a)) →
      ∀ U J : Finset ι, Disjoint U J → ∀ a b : (x : ι) → S x,
        conditionalProbability p (fun σ => ∀ x ∈ J, σ x = a x)
          (fun σ => ∀ x ∈ U, σ x = b x) ≥ α ^ U.card

/-- `l:planeenergy`, lines 736–744: reindex subsets of a finite physical
volume by its subtype. The cardinal of U is preserved using U⊆W; extension
outside W never enters an event. -/
def PlaneAssignmentReindexStatement : Prop :=
  ∀ W : Finset Plane, ∀ p : Weight (PlaneConfiguration W), ∀ α : ℝ,
    (∀ U J : Finset W, Disjoint U J → ∀ a b : PlaneConfiguration W,
      conditionalProbability p (fun σ => ∀ x ∈ J, σ x = a x)
        (fun σ => ∀ x ∈ U, σ x = b x) ≥ α ^ U.card) →
    ∀ U J : Finset Plane, U ⊆ W → J ⊆ W → Disjoint U J → ∀ a b : Plane → IcoLetter,
      conditionalProbability p (fun σ => ∀ x ∈ J, extendLetters σ x = a x)
        (fun σ => ∀ x ∈ U, extendLetters σ x = b x) ≥ α ^ U.card

/-- `l:planeenergy`, lines 747–759: every boundary factor is absorbed into
a positive endpoint weight. Thus the reference is a positive product law,
including the product over an empty volume. -/
def PlaneProductReferenceStatement : Prop :=
  interactionBounds →
  ∀ κ : Plane → Fin 3, ProperPlaneColouring κ → ∀ W : Finset Plane,
    ∀ η : FrameBoundary W,
      (∀ x : W, PositiveProbability (normalize (planeSiteWeight κ W η x))) ∧
      PositiveProbability (planeProductReference κ W η)

/-- `l:planeenergy`, lines 760–765: regroup crossing factors by their endpoint
and cancel the local normalizers. All remaining interactions are internal. -/
def BoundaryAbsorptionStatement : Prop :=
  interactionBounds →
  ∀ κ : Plane → Fin 3, ProperPlaneColouring κ → ∀ W : Finset Plane,
    ∀ η : FrameBoundary W,
      planeLaw κ W η = normalize (fun σ => planeProductReference κ W η σ * planeInteraction κ W σ)

/-- `l:planeenergy`, lines 764–770, 784–786: bound the internal interaction
product, prove its positive mean, and cancel that same mean in m/M.
The supplied product-law and absorption premises are explicit finite facts. -/
def PlaneDensityBoundsStatement : Prop :=
  interactionBounds →
  ∀ κ : Plane → Fin 3, ProperPlaneColouring κ → ∀ W : Finset Plane,
    ∀ η : FrameBoundary W, PositiveProbability (planeProductReference κ W η) →
      (planeLaw κ W η = normalize
        (fun σ => planeProductReference κ W η σ * planeInteraction κ W σ)) →
      0 < planeInteractionMean κ W η ∧ 0 < planeDensityLower κ W η ∧
      0 < planeDensityUpper κ W η ∧
      (∀ σ, planeDensityLower κ W η * planeProductReference κ W η σ ≤ planeLaw κ W η σ) ∧
      (∀ σ, planeLaw κ W η σ ≤ planeDensityUpper κ W η * planeProductReference κ W η σ) ∧
      planeDensityLower κ W η / planeDensityUpper κ W η = frameRatio ^ (internalBonds W).card

/-- Appendix A `l:density`, used at sec3 lines 772–782: compare variance by
its minimum over constant centres. Probability normalization is explicit. -/
def DensityVarianceStatement : Prop :=
  ∀ (Ω : Type) [Fintype Ω], ∀ p q : Weight Ω,
    PositiveProbability p → PositiveProbability q → ∀ M : ℝ, 0 ≤ M →
      (∀ σ, q σ ≤ M * p σ) → ∀ f, variance q f ≤ M * variance p f

/-- Appendix A `l:density`, sec3 lines 779–780: variational formula for the
integrated single-site conditional variance. Compare unnormalized fibre
energies before minimizing, so only one density ratio is lost. -/
def DensityDirichletStatement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι], ∀ S : ι → Type,
    ∀ (_ : ∀ x, Fintype (S x)), ∀ p q : Weight ((x : ι) → S x),
      PositiveProbability p → PositiveProbability q → ∀ m : ℝ, 0 ≤ m →
        (∀ σ, m * p σ ≤ q σ) → ∀ f, m * dirichlet p f ≤ dirichlet q f

/-- Appendix A `l:density`, sec3 line 781: complex Efron–Stein/product
Poincare inequality, with rate one per site. Finite dependent alphabets,
empty site sets, and one-letter alphabets are included. -/
def ProductPoincareStatement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι], ∀ S : ι → Type,
    ∀ (_ : ∀ x, Fintype (S x)), ∀ p : (x : ι) → Weight (S x),
      (∀ x, PositiveProbability (p x)) → PoincareLower (fun σ => ∏ x, p x (σ x)) 1

theorem positiveNormalization : PositiveNormalizationStatement := by
  classical
  intro Ω _ _ w hw
  have hz : 0 < ∑ σ, w σ := Finset.sum_pos (fun σ _ => hw σ) Finset.univ_nonempty
  refine ⟨fun σ => div_pos (hw σ) hz, ?_⟩
  simp [AKLT.Defs.normalize, ← Finset.sum_div, ne_of_gt hz]

end AKLT.Blueprint.Q
