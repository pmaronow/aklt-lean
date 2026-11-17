module
public import AKLT.Blueprint.Gap.NodesPeriodic

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
set_option maxHeartbeats 800000
open scoped BigOperators
open AKLT.Defs AKLT.Challenge
attribute [local instance] Classical.propDecidable
namespace AKLT.Blueprint.Gap
local instance (α : Type) : DecidableEq α := Classical.decEq α

/-- `l:stopped`, sec4:80-83. The fourth-power geometry threshold implies s≥16;
monotonicity of two square roots suffices, without real fractional-power identities. -/
def ThresholdSpacingStatement : Prop :=
  ∀ l u, geometryThreshold l ≤ u → 16 ≤ shellSpacing u

/-- `t:mainW`, sec4:521-526. H is the sum of the frozen orthogonal projections.
Its symmetry and B∈ker H force every nonzero-eigenvalue eigenvector orthogonal to B. -/
def GroundOrthogonalityStatement : Prop :=
  ∀ L N : Size, B L N ∈ LinearMap.ker (H L N) →
    ∀ μ : ℝ, μ ≠ 0 → ∀ ψ : Hilbert L N, H L N ψ = (μ : ℂ) • ψ →
      inner ℂ (B L N) ψ = 0

/-- `t:mainW`, sec4:511-519. On a nonzero eigenvector the energy is μ‖ψ‖²;
divide the coercivity inequality by its strictly positive squared norm. -/
def RayleighBoundStatement : Prop :=
  ∀ L N : Size, ∀ c : ℝ,
    (∀ ψ : Hilbert L N, inner ℂ (B L N) ψ = 0 →
      c * ‖ψ‖^2 ≤ (inner ℂ ψ (H L N ψ)).re) →
    ∀ μ : ℝ, (∀ ψ : Hilbert L N, H L N ψ = (μ : ℂ) • ψ → inner ℂ (B L N) ψ = 0) →
      (H L N).HasEigenvalue (μ : ℂ) → c ≤ μ

theorem groundOrthogonality : GroundOrthogonalityStatement := by
  intro L N hB μ hμ ψ hψ
  have hsym : (H L N).IsSymmetric := by
    apply LinearMap.isSymmetric_sum
    intro e _
    exact (spin4Space e).starProjection_isSymmetric
  have hzero : H L N (B L N) = 0 := hB
  have hi := hsym (B L N) ψ
  rw [hzero, hψ, inner_zero_left, inner_smul_right] at hi
  exact (mul_eq_zero.mp hi.symm).resolve_left (by exact_mod_cast hμ)

theorem rayleighBound : RayleighBoundStatement := by
  intro L N c hc μ horth hμ
  obtain ⟨ψ, hψ⟩ := hμ.exists_hasEigenvector
  have he := hc ψ (horth ψ hψ.apply_eq_smul)
  rw [hψ.apply_eq_smul, inner_smul_right, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at he
  have hi : (inner ℂ ψ ψ).re = ‖ψ‖^2 := (norm_sq_eq_re_inner (𝕜 := ℂ) ψ).symm
  rw [hi] at he
  have he' : c * ‖ψ‖^2 ≤ μ * ‖ψ‖^2 := he
  exact (mul_le_mul_iff_left₀ (sq_pos_of_pos (norm_pos_iff.mpr hψ.2))).mp he'

/-- Assembled interface for l:stopped, not an additional open leaf. -/
def StoppedCouplingStatement : Prop :=
  ∀ P : PlaneSpec, RegularSpec P → ∀ l p Mstar α,
    0 < α → α ≤ 1 → SpecEnergy P α → SpecWindow P l p Mstar →
      StoppedEstimate P l p Mstar α

/-- Assembled interface for l:hamming at a preselected scale; the choice of n is
separate, so n can be shared across every coloring. -/
def HammingAtScaleStatement : Prop :=
  ∀ P : PlaneSpec, RegularSpec P → ∀ l p Mstar α,
    0 < α → α ≤ 1 → SpecEnergy P α → SpecWindow P l p Mstar →
    ∀ n, ScaleConditions l Mstar (min (1/2) (p * α^(16*l))) n →
      HammingEstimate P (n^8) (((n^8 : ℕ) : ℝ)/1000)

/-- Assembled Appendix l:contraction interface. All blocks are labeled and the
number of labels is positive; no nontrivial-state-space premise is needed. -/
def FiniteContractionStatement : Prop :=
  ∀ (ι J : Type) [Fintype ι] [DecidableEq ι] [Fintype J] [Nonempty J]
    (S : ι → Type) [∀ x, Fintype (S x)] [∀ x, Nonempty (S x)]
    (p : Weight (Config S)), PositiveProbability p → ∀ B : J → Finset ι,
    ∀ c : ℝ, 0 < c → c ≤ Fintype.card J →
    (∀ σ τ, hamming σ τ = 1 →
      ∃ d : Coupling (blockAverage p B σ) (blockAverage p B τ),
        couplingCost d ≤ 1 - c / Fintype.card J) → BlockGap p B c

/-- Assembled Appendix l:comparison interface in multiplicative form. t>0 avoids
an artificial division-by-zero case; nonempty labeled physical blocks satisfy it. -/
def BlockComparisonStatement : Prop :=
  ∀ (ι J : Type) [Fintype ι] [DecidableEq ι] [Fintype J]
    (S : ι → Type) [∀ x, Fintype (S x)] [∀ x, Nonempty (S x)]
    (p : Weight (Config S)), PositiveProbability p → ∀ B : J → Finset ι,
    ∀ (t : ℕ) (g c : ℝ), 0 < t → 0 < g → 0 < c →
    (∀ x, (Finset.univ.filter fun a => x ∈ B a).card ≤ t) →
    (∀ a σ, PoincareLower (blockLaw p (B a) σ) g) → BlockGap p B c →
      PoincareLower p (c*g/t)

/-- Assembled t:periodic, retaining both the unnormalized block gap and the
single-site gap. The strict contraction premise appears exactly as in the paper. -/
def PeriodicCriterionStatement : Prop :=
  ∀ (L N : Size) (S : Site L N → Type) [∀ x, Fintype (S x)] [∀ x, Nonempty (S x)]
    (μ : Weight (Config S)), PositiveProbability μ →
    ∀ M g K, 1 ≤ M → 2*M+3 ≤ L.val → 2*M+3 ≤ N.val → 0 < g → 0 ≤ K →
    TorusRangeOne μ M → UniformBlockGap μ M g → BlockInfluence μ M K →
    (haloCount M : ℝ)*K < (volumeCount M : ℝ) →
      BlockGap μ (torusSquare L N M) ((volumeCount M : ℝ)-(haloCount M : ℝ)*K) ∧
      PoincareLower μ (g*(1-(haloCount M : ℝ)*K/(volumeCount M : ℝ)))

/-- `l:surgery`, app-finite:145-157. Forget strictness of the pointwise
probability bound while keeping the same normalization. This is already proved. -/
def PositiveToProbabilityStatement : Prop :=
  ∀ (Ω : Type) [Fintype Ω] (p : Weight Ω), PositiveProbability p → Probability p

theorem positiveToProbability : PositiveToProbabilityStatement := by
  intro Ω _ p hp
  exact ⟨fun x => (hp.1 x).le, hp.2⟩

/-- `l:stopped`, sec4:115. The product initial law has total mass one. -/
def IndependentPairsStatement : Prop :=
  ∀ (Ω : Type) [Fintype Ω] (p q : Weight Ω), Probability p → Probability q →
    Probability (independentPairs p q)

theorem independentPairsProbability : IndependentPairsStatement := by
  intro Ω _ p q hp hq
  refine ⟨fun ω => mul_nonneg (hp.1 ω.1) (hq.1 ω.2), ?_⟩
  simp only [independentPairs, Fintype.sum_prod_type, ← Finset.mul_sum, hq.2, mul_one, hp.2]

/-- `l:stopped`, sec4:75-78. Equal full laws have a zero-cost diagonal coupling. -/
def DiagonalCouplingStatement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (S : ι → Type) [∀ x, Fintype (S x)]
    (p : Weight (Config S)), Probability p → ∃ c : Coupling p p, couplingCost c = 0

theorem diagonalCoupling : DiagonalCouplingStatement := by
  intro ι _ _ S _ p hp
  let c : Coupling p p := {
    mass := fun σ τ => if σ = τ then p σ else 0
    nonnegative := fun σ τ => by split_ifs <;> simp_all [hp.1]
    first_marginal := fun σ => by simp
    second_marginal := fun τ => by simp }
  refine ⟨c, ?_⟩
  simp [couplingCost, c, hamming]

/-- `l:stopped`/`l:hamming`, sec4:60,239-248. All success parameters lie in the
claimed intervals; min(1/2,delta) is positive even when delta=1. -/
def DeltaBoundsStatement : Prop :=
  ∀ (l : ℕ) (p α : ℝ), 0 < p → p ≤ 1 → 0 < α → α ≤ 1 →
    0 < p*α^(16*l) ∧ p*α^(16*l) ≤ 1 ∧
    0 < min (1/2) (p*α^(16*l)) ∧ min (1/2) (p*α^(16*l)) ≤ 1/2 ∧
    min (1/2) (p*α^(16*l)) ≤ p*α^(16*l)

theorem deltaBounds : DeltaBoundsStatement := by
  intro l p α hp hp1 hα hα1
  have hpow : α^(16*l) ≤ 1 := pow_le_one₀ hα.le hα1
  exact ⟨mul_pos hp (pow_pos hα _), (mul_le_mul hp1 hpow (pow_nonneg hα.le _) (by norm_num)).trans_eq (one_mul 1),
    lt_min (by norm_num) (mul_pos hp (pow_pos hα _)), min_le_left _ _, min_le_right _ _⟩

/-- `l:stopped`, sec4:193-196. Larger numbers of trials decrease powers with
base in [0,1], including base zero; apply monotonicity of natural powers. -/
def PowerCountStatement : Prop :=
  ∀ b : ℝ, 0 ≤ b → b ≤ 1 → ∀ m n : ℕ, m ≤ n → b^n ≤ b^m

theorem powerCount : PowerCountStatement := by
  intro b hb hb1 m n hmn
  exact pow_le_pow_of_le_one hb hb1 hmn

/-- `t:periodic`, sec4:395-402. Lowering the Poincare constant preserves its
form inequality because variance is a sum of nonnegative squared terms. -/
def PoincareMonotoneStatement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (S : ι → Type) [∀ x, Fintype (S x)]
    (p : Weight (Config S)), Probability p → ∀ g h : ℝ, g ≤ h →
      PoincareLower p h → PoincareLower p g

theorem poincareMonotone : PoincareMonotoneStatement := by
  intro ι _ _ S _ p hp g h hgh hh f
  have hv : 0 ≤ variance p f := Finset.sum_nonneg fun σ _ => mul_nonneg (hp.1 σ) (Complex.normSq_nonneg _)
  exact (mul_le_mul_of_nonneg_right hgh hv).trans (hh f)

/-- The rational periodic-budget calculation is already proved. -/
theorem periodicBudget : PeriodicBudgetStatement := by
  intro M _
  have hm : (0 : ℝ) ≤ M := Nat.cast_nonneg _
  have ht : 0 < (2*(M : ℝ)+1)^2 := sq_pos_of_pos (by linarith)
  have hn : (8*(M : ℝ)+8)*((M : ℝ)/1000) ≤ (2*(M : ℝ)+1)^2/500 := by nlinarith
  have hq : (8*(M : ℝ)+8)*((M : ℝ)/1000)/(2*(M : ℝ)+1)^2 ≤ 1/500 :=
    (div_le_iff₀ ht).mpr (by nlinarith)
  simp only [volumeCount, haloCount, Nat.cast_pow, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  exact ⟨ht, by nlinarith, by linarith⟩

/-- Minimal finite-library inputs for the top assembly; this only bundles closed Props. -/
def FiniteAssemblyLeaves : Prop :=
  BlockAverageFormStatement ∧ LipschitzCouplingStatement ∧ LipschitzEigenvalueStatement ∧
  ReversibleEigenvalueGapStatement ∧ ConditionalBlockComparisonStatement ∧ MultiplicityEstimateStatement

/-- Minimal shell and scale inputs, each a closed writer obligation. -/
def ShellAssemblyLeaves : Prop :=
  ShellRowStatement ∧ TraceMarginalsStatement ∧ TrialCountStatement ∧ ShellAbsorptionStatement ∧
  FiniteTrialFailureStatement ∧ TraceDisagreementStatement ∧ ThresholdSpacingStatement ∧
  ScaleGeometryStatement ∧ BinomialTailStatement ∧ HammingCardinalityStatement ∧ HammingBudgetStatement ∧
  StoppedHammingConversionStatement ∧ FarBoundaryEqualityStatement ∧ ScaleExistenceStatement

/-- Minimal periodic counting and local gauge inputs, each a closed writer obligation. -/
def PeriodicAssemblyLeaves : Prop :=
  ContainingBlockCountStatement ∧ ExteriorBlockCountStatement ∧ BlockVolumeBoundStatement ∧
  PeriodicNeighborCouplingStatement ∧ FrameSpecRegularityStatement ∧ FrameSpecEnergyStatement ∧
  FrameWindowTransferStatement ∧ TorusColorStatement ∧ PullbackColorStatement ∧ HaloInjectionStatement ∧
  LiftBondStatement ∧ BoxCoordinatesStatement ∧ BoxGaugeLawStatement ∧ TorusRangeTransferStatement ∧
  SquareInternalEdgesStatement ∧ ProductPoincareTransportStatement ∧ ProductCouplingTransportStatement

#print axioms periodicBudget

#print axioms groundOrthogonality
#print axioms rayleighBound
#print axioms positiveToProbability
#print axioms independentPairsProbability
#print axioms diagonalCoupling
#print axioms deltaBounds
#print axioms powerCount
#print axioms poincareMonotone

end AKLT.Blueprint.Gap
