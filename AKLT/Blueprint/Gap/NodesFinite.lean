import AKLT.Blueprint.Gap.Definitions

/-! Writer-sized closed obligations for Appendix a:finite. Type quantifiers and finite,
nonempty alphabet instances are explicit; no obligation assumes another named leaf. -/

noncomputable section
set_option maxHeartbeats 800000
open scoped BigOperators
open AKLT.Defs AKLT.Challenge
attribute [local instance] Classical.propDecidable
namespace AKLT.Blueprint.Gap
local instance (α : Type) : DecidableEq α := Classical.decEq α

/-- `l:CE`, app-finite:35-46. Group the finite sum by the exterior fibre; strict
positivity makes its denominator positive. Also identify the full-state kernel mean. -/
def FibreNormalizationStatement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (S : ι → Type) [∀ x, Fintype (S x)]
    [∀ x, Nonempty (S x)] (p : Weight (Config S)), PositiveProbability p →
    ∀ U σ, Probability (fibre p U σ) ∧ PositiveProbability (blockLaw p U σ) ∧
      ∀ f, conditionalExpectation p U f σ = complexMean (fibre p U σ) f

/-- `l:CE`, app-finite:35-52. Conditional means are idempotent, preserve constants
and the original mean, and are self-adjoint for the weighted scalar product. -/
def ConditionalProjectionStatement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (S : ι → Type) [∀ x, Fintype (S x)]
    [∀ x, Nonempty (S x)] (p : Weight (Config S)), PositiveProbability p → ∀ U,
      (∀ f, conditionalExpectation p U (conditionalExpectation p U f) = conditionalExpectation p U f) ∧
      conditionalExpectation p U (fun _ => 1) = (fun _ => 1) ∧
      (∀ f, complexMean p (conditionalExpectation p U f) = complexMean p f) ∧
      ∀ f h, weightedInner p f (conditionalExpectation p U h) =
        weightedInner p (conditionalExpectation p U f) h

/-- `l:CE`, app-finite:47-64. Orthogonal decomposition gives the Dirichlet identity
and total variance for complex functions. Empty/full blocks are included. -/
def ConditionalVarianceStatement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (S : ι → Type) [∀ x, Fintype (S x)]
    [∀ x, Nonempty (S x)] (p : Weight (Config S)), PositiveProbability p → ∀ U f,
      (weightedInner p f (fun σ => f σ - conditionalExpectation p U f σ)).re = blockDirichlet p U f ∧
      expectation p (conditionalVariance p U f) = blockDirichlet p U f ∧
      variance p f = blockDirichlet p U f + variance p (conditionalExpectation p U f)

/-- `l:finitecoupling`, app-finite:87-104. Sum |p-q|=p+q-2 min; branch at overlap=1
when constructing the residual product, so no zero denominator occurs. -/
def MaximalCouplingStatement : Prop :=
  ∀ (Ω : Type) [Fintype Ω] (p q : Weight Ω), Probability p → Probability q →
    totalVariation p q = 1 - ∑ x, min (p x) (q x) ∧
    ∃ c : Coupling p q, (∑ x, ∑ y, if x = y then 0 else c.mass x y) = totalVariation p q

/-- `l:finitecoupling`, app-finite:101-112. A coupling's diagonal mass is bounded
by the overlap; finite pushforward decreases half-L1 total variation. -/
def CouplingMarginalTVStatement : Prop :=
  ∀ (Ω Ξ : Type) [Fintype Ω] [Fintype Ξ] (p q : Weight Ω), Probability p → Probability q →
    (∀ c : Coupling p q, totalVariation p q ≤ ∑ x, ∑ y, if x = y then 0 else c.mass x y) ∧
    ∀ r : Ω → Ξ, totalVariation (marginal p r) (marginal q r) ≤ totalVariation p q

/-- `l:finitecoupling`, app-finite:114-128. Lift a given marginal coupling by
conditional residual laws. Zero marginal fibres have zero mass and are branched off. -/
def MarginalCompletionStatement : Prop :=
  ∀ (Ω Ξ : Type) [Fintype Ω] [Fintype Ξ] (p q : Weight Ω), Probability p → Probability q →
    ∀ r : Ω → Ξ, ∀ c : Coupling (marginal p r) (marginal q r),
    ∃ d : Coupling p q, ∀ a b,
      (∑ x, ∑ y, if r x = a ∧ r y = b then d.mass x y else 0) = c.mass a b

/-- `l:finitecoupling`, app-finite:120-128. Pointwise d_H ≤ |V\Q|+|V|1_disagree(Q)
and the coupling marginals give this estimate for the same full-law coupling. -/
def HammingLocalizationStatement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (S : ι → Type) [∀ x, Fintype (S x)]
    (p q : Weight (Config S)), Probability p → Probability q → ∀ c : Coupling p q,
    ∀ U : Finset ι, couplingCost c ≤ ((Finset.univ \ U).card : ℝ) +
      (Fintype.card ι : ℝ) * disagreement c U

/-- `l:finitecoupling`, app-finite:126-130. Sum the common minorant in the overlap
formula. The endpoints p0=0 and p0=1 require no separate positive residual law. -/
def CommonMinorizationStatement : Prop :=
  ∀ (Ω : Type) [Fintype Ω] (p q ν : Weight Ω), Probability p → Probability q → Probability ν →
    ∀ t : ℝ, 0 ≤ t → t ≤ 1 → (∀ x, t * ν x ≤ p x ∧ t * ν x ≤ q x) →
      totalVariation p q ≤ 1 - t

/-- `l:surgery`, app-finite:145-159. Sum the first marginal of each row, then use
stationarity of the conditional kernel; pair dependence of a row is unrestricted. -/
def SurgeryPreservationStatement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (S : ι → Type) [∀ x, Fintype (S x)]
    [∀ x, Nonempty (S x)] (p q : Weight (Config S)), PositiveProbability p → PositiveProbability q →
    ∀ U, ∀ c : Coupling p q, ∀ R : (σ τ : Config S) → Coupling (fibre p U σ) (fibre q U τ),
      ∃ d : Coupling p q, ∀ σ τ,
        d.mass σ τ = ∑ a, ∑ b, c.mass a b * (R a b).mass σ τ

/-- `l:stopped`, sec4:125-157; `l:finitecoupling`, app-finite:114-124.
Maximally couple B, complete the two laws independently, then resample A independently
conditional on each complement. The assignment bound gives alpha^(2|A|) conditional
success without disturbing the B agreement. This is the reusable quantitative part
of a single shell row, separated from plane geometry and the stopping argument. -/
def ConditionalPatchCouplingStatement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (S : ι → Type) [∀ x, Fintype (S x)]
    [∀ x, Nonempty (S x)] (p q : Weight (Config S)), PositiveProbability p → PositiveProbability q →
    ∀ (A B : Finset ι) (α t : ℝ), Disjoint A B → 0 < α → α ≤ 1 → 0 ≤ t → t ≤ 1 →
    AssignmentBound p α → AssignmentBound q α →
    totalVariation (marginal p (restrict B)) (marginal q (restrict B)) ≤ 1-t →
      ∃ c : Coupling p q, disagreement c (A ∪ B) ≤ 1-t*α^(2*A.card)

/-- The internal interaction product, with each unoriented bond counted once. -/
def planeInteraction (κ : Plane → Fin 3) (W : Finset Plane) (σ : PlaneConfiguration W) : ℝ :=
  ∏ e ∈ internalBonds W,
    (1+dot (frameVector (κ e.1) (extendLetters σ e.1)) (frameVector (κ e.2) (extendLetters σ e.2)))

/-- `l:density`, app-finite:224-237. Absorb all fixed boundary factors into the
one-site weights and normalize those weights individually. Exterior corners with no
crossing bond contribute no factor; only internal bonds remain in the interaction. -/
def FrameProductReferenceStatement : Prop :=
  (∀ i j : Fin 3, i ≠ j → ∀ a b : IcoLetter, 0 < 1+dot (frameVector i a) (frameVector j b)) →
  ∀ κ : Plane → Fin 3, ProperPlaneColouring κ → ∀ (W : Finset Plane) (η : FrameBoundary W),
    ∃ π : (x : W) → Weight IcoLetter, (∀ x, PositiveProbability (π x)) ∧
    ∃ Z : ℝ, 0 < Z ∧ Z = expectation (fun σ => ∏ x, π x (σ x)) (planeInteraction κ W) ∧
      ∀ σ, planeLaw κ W η σ = (∏ x, π x (σ x)) * planeInteraction κ W σ / Z

/-- `l:density`, app-finite:238-250. Multiply the per-edge bounds over the
internal bonds only, including the empty product at zero sites. -/
def FrameInteractionBoundsStatement : Prop :=
  (∀ i j : Fin 3, i ≠ j → ∀ a b : IcoLetter,
    frameBound ≤ 1+dot (frameVector i a) (frameVector j b) ∧
    1+dot (frameVector i a) (frameVector j b) ≤ 2-frameBound) →
  0 < frameBound → frameBound < 1 → ∀ κ : Plane → Fin 3, ProperPlaneColouring κ →
    ∀ W σ, frameBound^(internalBonds W).card ≤ planeInteraction κ W σ ∧
      planeInteraction κ W σ ≤ (2-frameBound)^(internalBonds W).card

/-- `l:density`, app-finite:239-251. For a supplied positive product reference,
pointwise interaction bounds give density bounds lo/Z and hi/Z for the normalized
law. All three denominators (site normalizers, Z, hi) are positive. -/
def NormalizedInteractionStatement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (S : ι → Type) [∀ x, Fintype (S x)]
    [∀ x, Nonempty (S x)] (π : (x : ι) → Weight (S x)), (∀ x, PositiveProbability (π x)) →
    ∀ (ψ : Config S → ℝ) (lo hi Z : ℝ), 0 < lo → 0 < hi →
      (∀ σ, lo ≤ ψ σ ∧ ψ σ ≤ hi) → 0 < Z → Z = expectation (fun σ => ∏ x, π x (σ x)) ψ →
      PositiveProbability (fun σ => (∏ x, π x (σ x))*ψ σ/Z) ∧
      ∀ σ, (lo/Z)*(∏ x, π x (σ x)) ≤ (∏ x, π x (σ x))*ψ σ/Z ∧
        (∏ x, π x (σ x))*ψ σ/Z ≤ (hi/Z)*(∏ x, π x (σ x))

/-- `l:density`, app-finite:224-251, for either sign on every internal bond.
Site weights include all fixed boundary factors. Normalize them to a product law,
bound the signed interaction between b^e and (2-b)^e, and apply the one-ratio density
comparison. No positivity statement is made for arbitrary unit-vector pins. -/
def SignedFrameBlockStatement : Prop :=
  0 < frameBound → frameBound < 1 →
  (∀ i j : Fin 3, i ≠ j → ∀ a b : IcoLetter,
    frameBound ≤ 1+dot (frameVector i a) (frameVector j b) ∧
    1+dot (frameVector i a) (frameVector j b) ≤ 2-frameBound ∧
    frameBound ≤ 1-dot (frameVector i a) (frameVector j b) ∧
    1-dot (frameVector i a) (frameVector j b) ≤ 2-frameBound) →
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (κ : ι → Fin 3) (E : Finset (ι × ι)),
    (∀ e ∈ E, κ e.1 ≠ κ e.2) → ∀ (positiveSign : ι × ι → Bool) (h : ι → Weight IcoLetter),
    (∀ x a, 0 < h x a) →
    PoincareLower (normalize (fun σ : ι → IcoLetter => (∏ x, h x (σ x)) *
      ∏ e ∈ E, if positiveSign e then
        1+dot (frameVector (κ e.1) (σ e.1)) (frameVector (κ e.2) (σ e.2))
      else 1-dot (frameVector (κ e.1) (σ e.1)) (frameVector (κ e.2) (σ e.2))))
      (frameRatio^E.card)

/-- `l:density`, app-finite:177-197. Subtract the conditional mean (or constant
mean) and expand the square; the cross term vanishes by fibre averaging. -/
def VariationalCenteringStatement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (S : ι → Type) [∀ x, Fintype (S x)]
    [∀ x, Nonempty (S x)] (p : Weight (Config S)), PositiveProbability p → ∀ f,
      (∀ z : ℂ, variance p f ≤ ∑ σ, p σ * Complex.normSq (f σ - z)) ∧
      ∀ (U : Finset ι) (h : Config S → ℂ), (∀ σ τ, AgreeOutside U σ τ → h σ = h τ) →
        blockDirichlet p U f ≤ ∑ σ, p σ * Complex.normSq (f σ - h σ)

/-- `l:density`, app-finite:198-216. Enumerate sites; commuting coordinate
projections yield an orthogonal telescoping sum. Includes the zero-site product. -/
def ProductTensorizationStatement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (S : ι → Type) [∀ x, Fintype (S x)]
    [∀ x, Nonempty (S x)] (π : (x : ι) → Weight (S x)),
    (∀ x, PositiveProbability (π x)) → PoincareLower (fun σ => ∏ x, π x (σ x)) 1

/-- `l:density`, app-finite:180-220. Apply the two variational formulas to
pointwise mπ≤μ≤Mπ, and then tensorization. Only one density ratio is lost. -/
def DensityComparisonStatement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (S : ι → Type) [∀ x, Fintype (S x)]
    [∀ x, Nonempty (S x)] (π : (x : ι) → Weight (S x)) (μ : Weight (Config S)),
    (∀ x, PositiveProbability (π x)) → PositiveProbability μ →
    ∀ m M : ℝ, 0 < m → 0 < M → (∀ σ, m * (∏ x, π x (σ x)) ≤ μ σ ∧
      μ σ ≤ M * (∏ x, π x (σ x))) →
    (∀ f, m * dirichlet (fun σ => ∏ x, π x (σ x)) f ≤ dirichlet μ f ∧
      variance μ f ≤ M * variance (fun σ => ∏ x, π x (σ x)) f) ∧ PoincareLower μ (m / M)

/-- `l:comparison`, app-finite:270-286. Integrate the conditional block Poincare
inequality and identify the nested single-site fibre with the original one-site fibre. -/
def ConditionalBlockComparisonStatement : Prop :=
  ∀ (ι J : Type) [Fintype ι] [DecidableEq ι] [Fintype J]
    (S : ι → Type) [∀ x, Fintype (S x)] [∀ x, Nonempty (S x)]
    (p : Weight (Config S)), PositiveProbability p → ∀ B : J → Finset ι,
    ∀ g : ℝ, 0 < g → (∀ a σ, PoincareLower (blockLaw p (B a) σ) g) → ∀ f,
      g * blockForm p B f ≤ ∑ x, ((Finset.univ.filter fun a => x ∈ B a).card : ℝ) *
        blockDirichlet p {x} f

/-- `l:comparison`, app-finite:280-294. Nonnegative one-site forms and an explicit
multiplicity bound give g times the block form ≤ t times the single-site form. -/
def MultiplicityEstimateStatement : Prop :=
  ∀ (ι J : Type) [Fintype ι] [DecidableEq ι] [Fintype J]
    (S : ι → Type) [∀ x, Fintype (S x)] (p : Weight (Config S)), PositiveProbability p →
    ∀ (B : J → Finset ι) (t : ℕ), (∀ x, (Finset.univ.filter fun a => x ∈ B a).card ≤ t) →
    ∀ f, (∑ x, ((Finset.univ.filter fun a => x ∈ B a).card : ℝ) * blockDirichlet p {x} f) ≤
      (t : ℝ) * dirichlet p f

/-- `l:contraction`, app-finite:310-321. Change the differing coordinates one at
a time. The zero edge maximum is zero precisely for constant functions, even with
singleton alphabets and with no sites. -/
def HammingPathStatement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (S : ι → Type) [∀ x, Fintype (S x)] [∀ x, Nonempty (S x)]
    (f : Config S → ℝ), 0 ≤ lipschitz f ∧
    (∀ σ τ, |f σ - f τ| ≤ lipschitz f * hamming σ τ) ∧
    (lipschitz f = 0 ↔ ∃ c, ∀ σ, f σ = c)

/-- `l:contraction`, app-finite:321-326. Test the neighbour-output couplings on
f and take the maximum of finitely many one-coordinate oscillations. -/
def LipschitzCouplingStatement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (S : ι → Type) [∀ x, Fintype (S x)] [∀ x, Nonempty (S x)]
    (K : Config S → Weight (Config S)), (∀ σ, Probability (K σ)) →
    ∀ r : ℝ, 0 ≤ r →
      (∀ σ τ, hamming σ τ = 1 → ∃ c : Coupling (K σ) (K τ), couplingCost c ≤ r) →
      ∀ f, lipschitz (kernelMean K f) ≤ r * lipschitz f

/-- `l:contraction`, app-finite:336-341. A nonzero real mean-zero eigenfunction
is nonconstant. Homogeneity of the finite edge maximum and Lipschitz contraction
bound its eigenvalue. This separates the path argument from diagonalization. -/
def LipschitzEigenvalueStatement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (S : ι → Type) [∀ x, Fintype (S x)]
    [∀ x, Nonempty (S x)] (p : Weight (Config S)) (K : Config S → Weight (Config S)),
    PositiveProbability p → ∀ r : ℝ, 0 ≤ r →
    (∀ f, lipschitz (kernelMean K f) ≤ r*lipschitz f) →
    ∀ (f : Config S → ℝ) (eigenvalue : ℝ), expectation p f = 0 → (∃ σ, f σ ≠ 0) →
      (∀ σ, kernelMean K f σ = eigenvalue*f σ) → eigenvalue ≤ r

/-- `l:contraction`, app-finite:328-348. Detailed balance conjugates to a real
symmetric matrix. Diagonalize its mean-zero restriction, expand the quadratic form,
and add the real and imaginary inequalities. The eigenvalue bound is local to this
one kernel, not a hypothesis asserting another closed leaf. -/
def ReversibleEigenvalueGapStatement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (S : ι → Type) [∀ x, Fintype (S x)]
    [∀ x, Nonempty (S x)] (p : Weight (Config S)) (K : Config S → Weight (Config S)),
    PositiveProbability p → Reversible p K → ∀ A c : ℝ, 0 < A → 0 < c → c ≤ A →
    (∀ (f : Config S → ℝ) (eigenvalue : ℝ), expectation p f = 0 → (∃ σ, f σ ≠ 0) →
      (∀ σ, kernelMean K f σ = eigenvalue*f σ) → eigenvalue ≤ 1-c/A) →
    ∀ f, c * variance p f ≤ kernelForm p K A f

/-- Assembled spectral interface for l:contraction; not an additional open leaf. -/
def ReversibleSpectralStatement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (S : ι → Type) [∀ x, Fintype (S x)] [∀ x, Nonempty (S x)]
    (p : Weight (Config S)) (K : Config S → Weight (Config S)),
    PositiveProbability p → Reversible p K → ∀ A c : ℝ, 0 < A → 0 < c → c ≤ A →
    (∀ f, lipschitz (kernelMean K f) ≤ (1 - c / A) * lipschitz f) →
    ∀ f, c * variance p f ≤ kernelForm p K A f

/-- `l:contraction`/`l:CE`, app-finite:65-66,328-330. An average of conditional
projections is reversible and has exactly the labelled sum as its A(I-P) form. -/
def BlockAverageFormStatement : Prop :=
  ∀ (ι J : Type) [Fintype ι] [DecidableEq ι] [Fintype J] [Nonempty J]
    (S : ι → Type) [∀ x, Fintype (S x)] [∀ x, Nonempty (S x)]
    (p : Weight (Config S)), PositiveProbability p → ∀ B : J → Finset ι,
      Reversible p (blockAverage p B) ∧ ∀ f,
        kernelForm p (blockAverage p B) (Fintype.card J) f = blockForm p B f

/-- `l:boxlift` used in `t:mainW`, sec4:459-465. Change variables in the finite
sums; the coordinate equality equivalence identifies every one-site fibre. -/
def ProductPoincareTransportStatement : Prop :=
  ∀ (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (S : ι → Type) (T : κ → Type) [∀ x, Fintype (S x)] [∀ y, Fintype (T y)]
    (e : ProductChange S T) (p : Weight (Config S)) (q : Weight (Config T)),
    Carries e p q → ∀ g, PoincareLower q g → PoincareLower p g

/-- `l:boxlift` used in `t:mainW`, sec4:478-489. Pull a coupling through the same
coordinatewise bijection in both components; the Hamming cost is unchanged. -/
def ProductCouplingTransportStatement : Prop :=
  ∀ (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (S : ι → Type) (T : κ → Type)
    [∀ x, Fintype (S x)] [∀ y, Fintype (T y)] (e : ProductChange S T)
    (p p' : Weight (Config S)) (q q' : Weight (Config T)),
    Carries e p q → Carries e p' q' → ∀ c : Coupling q q',
      ∃ d : Coupling p p', couplingCost d = couplingCost c

end AKLT.Blueprint.Gap
