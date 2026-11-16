import AKLT.Blueprint.Win.Defs

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.Blueprint.Win

/-- `e:windowfactor`, sec5-window.tex:154–174. Split configurations on F into configurations on B and G=F\B. With no exterior neighbour of B, products factor into the actual W_B and the complementary frame partition sum. -/
def FrameFibreSumStatement : Prop :=
  AKLT.Blueprint.Top.ThreeFramesStatement →
    ∀ κ : Plane → Fin 3, ProperPlaneColouring κ →
    ∀ F B : Finset Plane, B ⊆ F → NoBond (↑B) {z | z ∉ F} →
    ∀ unit : ∀ j a, normSq (frameVector j a) = 1,
    ∀ η : FrameBoundary F, ∀ s : PlaneConfiguration B,
    marginalNumerator κ F B η s = windowWeight κ B s *
      framePinnedSum κ (F \ B) ∅ (cutPins κ (F \ B) F B unit η s)

/-- `l:exact`, sec5-window.tex:171–174,775–778. Represent the complementary partition integrand as a polynomial with separate degree at most four. Apply the actual frame moment laws; the window configuration is held fixed. -/
def ComplementQuadratureStatement : Prop :=
  AKLT.Blueprint.Top.ThreeFramesStatement → AKLT.Blueprint.Top.ExactStatement →
    ∀ κ : Plane → Fin 3, ∀ G Y : Finset Plane, ∀ τ : PinAssignment G,
    framePinnedSum κ G Y τ = pinnedSum G Y τ (fun _ => 1)

/-- `e:windowfactor`, sec5-window.tex:166–177. Sum the unnormalized fibre numerators over the nonempty finite window product and move the positive original normalizer through each sum. -/
def MarginalNormalizationStatement : Prop :=
  ∀ κ : Plane → Fin 3, ∀ F B : Finset Plane, B ⊆ F →
    ∀ η : FrameBoundary F, 0 < ∑ σ : PlaneConfiguration F, planeWeight κ F η σ →
    planeMarginal κ F B η = normalize (marginalNumerator κ F B η)

/-- `e:cutfactorization`, sec5-window.tex:179–191. Use the partition of G\X and absence of interpiece bonds to split the finite product sum. Component sums remove G\H from original G and therefore carry no new legs into X. -/
def OriginalFactorizationStatement : Prop :=
  ∀ F B X G₁ G₂ : Finset Plane, SeparatingCut F B X G₁ G₂ →
    ∀ τ : PinAssignment (F \ B),
    pinnedSum (F \ B) X τ (fun _ => 1) =
      componentSum (F \ B) G₁ τ * componentSum (F \ B) G₂ τ ∧
    freeSum (F \ B) X (fun _ => 1) =
      freeSum (F \ B) ((F \ B) \ G₁) (fun _ => 1) *
      freeSum (F \ B) ((F \ B) \ G₂) (fun _ => 1)

/-- `l:cut`, sec5-window.tex:179–184. On G₁ all retained original pins end in B; on G₂ all end outside F. Compare the component products term by term, discarding pins whose tails were removed. -/
def ComponentPinsStatement : Prop :=
  ∀ κ : Plane → Fin 3, ∀ F B X G₁ G₂ : Finset Plane,
    SeparatingCut F B X G₁ G₂ →
    ∀ unit : ∀ j a, normSq (frameVector j a) = 1,
    ∀ η ξ : FrameBoundary F, ∀ s t : PlaneConfiguration B,
    componentSum (F \ B) G₁ (cutPins κ (F \ B) F B unit η s) =
      componentSum (F \ B) G₁ (cutPins κ (F \ B) F B unit ξ s) ∧
    componentSum (F \ B) G₂ (cutPins κ (F \ B) F B unit η s) =
      componentSum (F \ B) G₂ (cutPins κ (F \ B) F B unit η t)

/-- `l:cut`, sec5-window.tex:155–163. Every actual frame bond of a proper colouring is bounded below by positive frameBound; finite site and bond products are positive, including an empty window. -/
def WindowWeightPositiveStatement : Prop :=
  AKLT.Blueprint.Top.ThreeFramesStatement →
    ∀ κ : Plane → Fin 3, ProperPlaneColouring κ →
    ∀ B : Finset Plane, ∀ s : PlaneConfiguration B, 0 < windowWeight κ B s

/-- `l:cut`, sec5-window.tex:192–213. Choose fixed exterior and window assignments. Factor the removed partition ratio, absorb the exterior-only positive factors into the normalizer, and take w(s)=W_B(s)Z_G₁(s). Expand logs only of positive partition sums. -/
def WindowRewriteStatement : Prop :=
  ∀ κ : Plane → Fin 3, ∀ F B X G₁ G₂ : Finset Plane,
    SeparatingCut F B X G₁ G₂ →
    ∀ unit : ∀ j a, normSq (frameVector j a) = 1,
    (∀ G Y : Finset Plane, ∀ τ : PinAssignment G,
      0 < pinnedSum G Y τ (fun _ => 1) ∧ 0 < freeSum G Y (fun _ => 1)) →
    (∀ s : PlaneConfiguration B, 0 < windowWeight κ B s) →
    (∀ η : FrameBoundary F,
      planeMarginal κ F B η = normalize (fun s => windowWeight κ B s *
        pinnedSum (F \ B) ∅ (cutPins κ (F \ B) F B unit η s) (fun _ => 1))) →
    (∀ τ : PinAssignment (F \ B),
      pinnedSum (F \ B) X τ (fun _ => 1) =
        componentSum (F \ B) G₁ τ * componentSum (F \ B) G₂ τ) →
    (∀ η ξ : FrameBoundary F, ∀ s t : PlaneConfiguration B,
      componentSum (F \ B) G₁ (cutPins κ (F \ B) F B unit η s) =
        componentSum (F \ B) G₁ (cutPins κ (F \ B) F B unit ξ s) ∧
      componentSum (F \ B) G₂ (cutPins κ (F \ B) F B unit η s) =
        componentSum (F \ B) G₂ (cutPins κ (F \ B) F B unit η t)) →
    ∃ w : Weight (PlaneConfiguration B), (∀ s, 0 < w s) ∧
      ∀ η : FrameBoundary F, planeMarginal κ F B η = normalize (fun s =>
        w s * Real.exp (-cutError (F \ B) X (cutPins κ (F \ B) F B unit η s)))

/-- `l:cut`, sec5-window.tex:202–217. Normalize the positive base weight. The tilted normalizer is between exp(−E) and exp(E) times the base normalizer, which proves both comparisons and full support. -/
def BoundedTiltStatement : Prop :=
  ∀ (Ω : Type) [Fintype Ω] [Nonempty Ω],
    ∀ w : Weight Ω, (∀ s, 0 < w s) → ∀ E : ℝ, 0 ≤ E →
    PositiveProbability (normalize w) ∧
    ∀ e : Ω → ℝ, (∀ s, |e s| ≤ E) →
    PositiveProbability (normalize (fun s => w s * Real.exp (-e s))) ∧
    ∀ s, Real.exp (-2 * E) * normalize w s ≤
      normalize (fun s => w s * Real.exp (-e s)) s ∧
      normalize (fun s => w s * Real.exp (-e s)) s ≤ Real.exp (2 * E) * normalize w s

/-- `l:cut`, sec5-window.tex:219–228. Use |a−b|=a+b−2min(a,b), sum both probability laws, and lower-bound their overlap by p₀ times the common reference probability. -/
def OverlapMinorizationStatement : Prop :=
  ∀ Ω : Type, ∀ _ : Fintype Ω, ∀ p q ν : Weight Ω,
    Probability p → Probability q → Probability ν → ∀ p₀ : ℝ, 0 ≤ p₀ →
    (∀ s, p₀ * ν s ≤ p s) → (∀ s, p₀ * ν s ≤ q s) →
    totalVariation p q ≤ 1 - p₀

/-- `l:threeframes`, sec5-window.tex:163–177. Every internal or exterior edge has differently coloured endpoints. Apply the positive lower bound from ThreeFramesStatement to every factor, then multiply. -/
def FrameWeightPositiveStatement : Prop :=
  AKLT.Blueprint.Top.ThreeFramesStatement →
    ∀ κ : Plane → Fin 3, ProperPlaneColouring κ → ∀ F : Finset Plane,
    ∀ η : FrameBoundary F, ∀ σ : PlaneConfiguration F, 0 < planeWeight κ F η σ

end AKLT.Blueprint.Win
