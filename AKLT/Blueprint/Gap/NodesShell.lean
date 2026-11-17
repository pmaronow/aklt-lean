module
public import AKLT.Blueprint.Gap.NodesFinite

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

/-- `l:stopped`, sec4:84-99. Extract the local geometric facts; the independent
Top hypothesis is used by the assembly, not assumed by this leaf. Nesting uses s≥16
and floor((j-1)s)≥(j-1)s-1>is. -/
def ShellNestingStatement : Prop :=
  ∀ a y u, 16 ≤ shellSpacing u → ∀ i j : ℤ, i + 2 ≤ j →
    farVolume a y u j ⊆ farVolume a y u (i + 1) ∧
    shell a y u (j - 1) ⊆ farVolume a y u (i + 1)

/-- `l:stopped`, sec4:100-113. Partial conditionals average full one-site fibers;
then induct over an ordering of the prescribed assignment sites. Positivity and
nonempty alphabets ensure every partial fiber has positive mass. -/
def FiniteEnergyChainStatement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (S : ι → Type) [∀ x, Fintype (S x)]
    [∀ x, Nonempty (S x)] (p : Weight (Config S)), PositiveProbability p →
    ∀ α : ℝ, 0 < α → α ≤ 1 →
    (∀ x σ a, α ≤ conditionalProbability p (AgreeOutside {x} σ) (fun τ => τ x = a)) →
      AssignmentBound p α

/-- `l:stopped`, sec4:115-160. One row of the shell surgery: identical resampling
when the predecessor agrees; otherwise maximal B coupling, independent completion,
then independent conditional A resampling. Skipped rows are point masses. This is
one surgery only, not the stopped iteration. The final index h+1 requires no W bound. -/
def ShellRowStatement : Prop :=
  ∀ (P : PlaneSpec), RegularSpec P → ∀ l p Mstar α,
    0 < α → α ≤ 1 → SpecEnergy P α → SpecWindow P l p Mstar →
    ∀ a u, max Mstar (geometryThreshold l) ≤ u → ∀ y,
    setDistance supDist y (↑(square a u) : Set Plane) = 1 → ShellGeometry l a y u →
    ∀ η ξ : Config P.Letter, (∀ z, z ≠ y → η z = ξ z) →
    ∀ h : ℕ, 4 ≤ h → (h : ℝ) ≤ shellSpacing u →
    ∀ (j : Fin h) ω, ∃ r, RowConditions P a y u l h p α η ξ j ω r

/-- `l:surgery` iterated, sec4:136-140. Sum a finite Markov trace by its last
coordinate, applying pair-dependent surgery preservation at each step, including skips. -/
def TraceMarginalsStatement : Prop :=
  ∀ (P : PlaneSpec), RegularSpec P → ∀ a y u l h p α η ξ,
    ∀ R : SurgeryKernels P a y u l h p α η ξ,
      Probability (surgeryTrace P a y u l h p α η ξ R) ∧
      ∃ c : Coupling (P.law (square a u) η) (P.law (square a u) ξ),
        ∀ σ τ, c.mass σ τ = marginal (surgeryTrace P a y u l h p α η ξ R)
          (fun t => t (Fin.last h)) (σ, τ)

/-- `l:stopped`, sec4:161-167. At most one exceptional index deletes at most two
trial positions. Keep natural subtraction under the explicit h≥4 hypothesis. -/
def TrialCountStatement : Prop :=
  ∀ a y u h, 4 ≤ h → (exceptionalIndices a y u).card ≤ 1 →
    h - 3 ≤ (trialTimes a y u h).card

/-- `l:stopped`, sec4:168-183. A successful trial followed by the unskipped next
step forces agreement, and nested later surgeries preserve it. All claims are on
positive-mass paths, so rows with zero transition weight need no support proof. -/
def ShellAbsorptionStatement : Prop :=
  ∀ (P : PlaneSpec) a y u l h p α η ξ, 16 ≤ shellSpacing u →
    ∀ R : SurgeryKernels P a y u l h p α η ξ,
    ∀ t, 0 < surgeryTrace P a y u l h p α η ξ R t →
      (∃ j ∈ trialTimes a y u h, shellAgreement P a y u h j (t j.succ)) →
      AgreeOn (farSites a y u ((h : ℝ) * shellSpacing u))
        (t (Fin.last h)).1 (t (Fin.last h)).2

/-- `l:stopped`, sec4:185-195. Condition on the complete past at each ordered
trial. Finite induction bounds failure by (1-delta)^|J| without independence of trials.
The endpoint delta=1 is included; empty J gives power zero. -/
def FiniteTrialFailureStatement : Prop :=
  ∀ (Ω : Type) [Fintype Ω] (m : ℕ) (initial : Weight (Ω × Ω)), Probability initial →
    ∀ K : Fin m → Ω × Ω → Weight (Ω × Ω), (∀ j ω, Probability (K j ω)) →
    ∀ (J : Finset (Fin m)) (E : Fin m → Ω × Ω → Prop) (δ : ℝ),
    0 ≤ δ → δ ≤ 1 → (∀ j ∈ J, ∀ ω, δ ≤ eventMass (K j ω) (E j)) →
      eventMass (traceLaw m initial K) (fun t => ∀ j ∈ J, ¬ E j (t j.succ)) ≤ (1-δ)^J.card

/-- `l:stopped`, sec4:181-198. Push the finite path law to its endpoint and bound
disagreement by the no-success event. The pointwise implication is required only on
positive-mass paths, and zero atoms contribute nothing. -/
def TraceDisagreementStatement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (S : ι → Type) [∀ x, Fintype (S x)]
    (m : ℕ) (w : Weight (PairTrace (Config S) m)), Probability w →
    ∀ (p q : Weight (Config S)) (c : Coupling p q),
    (∀ σ τ, c.mass σ τ = marginal w (fun t => t (Fin.last m)) (σ, τ)) →
    ∀ (U : Finset ι) (J : Finset (Fin m)) (E : Fin m → Config S × Config S → Prop),
    (∀ t, 0 < w t → (∃ j ∈ J, E j (t j.succ)) →
      AgreeOn U (t (Fin.last m)).1 (t (Fin.last m)).2) →
      disagreement c U ≤ eventMass w (fun t => ∀ j ∈ J, ¬ E j (t j.succ))

/-- `p:surgery`, sec4:210-226. Set h=floor(s), use hs≤sqrt(u), marginal coupling
TV and real-power antitonicity. The zero-base branch has s-4>0 and is explicit. -/
def TerminalRadiusStatement : Prop :=
  ∀ (P : PlaneSpec) l p Mstar α, 0 < α → α ≤ 1 → 0 < p → p ≤ 1 →
    StoppedEstimate P l p Mstar α →
    ∀ a u, max Mstar (geometryThreshold l) ≤ u → ∀ y,
    setDistance supDist y (↑(square a u) : Set Plane) = 1 →
    ∀ η ξ : Config P.Letter, (∀ z, z ≠ y → η z = ξ z) →
    totalVariation
      (specMarginal P (square a u) ((square a u).filter fun x => Real.sqrt u < (supDist x y : ℝ)) η)
      (specMarginal P (square a u) ((square a u).filter fun x => Real.sqrt u < (supDist x y : ℝ)) ξ) ≤
      (1 - p * α^(16*l)) ^ (shellSpacing u - 4 : ℝ)

/-- `l:hamming`, sec4:248-261. Archimedean choice above four explicit finite
thresholds. This choice has no torus, translate, coloring or boundary argument. -/
def ScaleExistenceStatement : Prop :=
  ∀ l Mstar : ℕ, ∀ d : ℝ, 0 < d → ∃ n : ℕ, ScaleConditions l Mstar d n

/-- `l:hamming`, sec4:263-282. Keep the twentieth binomial term and bound its
falling factors below by n/2. All reciprocal denominators are positive. -/
def BinomialTailStatement : Prop :=
  ∀ d : ℝ, 0 < d → d ≤ 1/2 → ∀ n : ℕ, 44 ≤ n →
    (1-d)^(n-3) ≤ (2^20 * (Nat.factorial 20 : ℝ)) / (d^20 * (n : ℝ)^20)

/-- `l:hamming`, sec4:284-291. Identify s=(n^8)^(1/4)=n², check all stopped
indices and thresholds before using the coupling. -/
def ScaleGeometryStatement : Prop :=
  ∀ l Mstar d n, ScaleConditions l Mstar d n →
    max Mstar (geometryThreshold l) ≤ n^8 ∧ 4 ≤ n ∧
    (n : ℝ) ≤ shellSpacing (n^8) ∧ (n : ℝ) * shellSpacing (n^8) = (n : ℝ)^3 ∧
    16 ≤ shellSpacing (n^8)

/-- `l:hamming`, sec4:294-302. Count a sup-ball and the square by coordinate
intervals; the upper bounds 25 n^6 and 25 n^16 deliberately have slack. -/
def HammingCardinalityStatement : Prop :=
  ∀ a y n, 1 ≤ n →
    ((Finset.univ \ farSites a y (n^8) ((n : ℝ)^3)).card : ℝ) ≤ 25*(n : ℝ)^6 ∧
    (Fintype.card (square a (n^8)) : ℝ) ≤ 25*(n : ℝ)^16

/-- `l:hamming`, sec4:303-310. Substitute the binomial tail bound and use n²≥50000
and n¹²d²⁰≥50000·2²⁰·20!. Split the budget into two n^8/2000 terms. -/
def HammingBudgetStatement : Prop :=
  ∀ l Mstar d n, 0 < d → d ≤ 1/2 → ScaleConditions l Mstar d n →
    (1-d)^(n-3) ≤ (2^20 * (Nat.factorial 20 : ℝ)) / (d^20 * (n : ℝ)^20) →
    25*(n : ℝ)^6 + 25*(n : ℝ)^16*(1-d)^(n-3) ≤ ((n^8 : ℕ) : ℝ)/1000

/-- `l:stopped` far-site clause / `l:hamming`, sec4:75-78,291-293. For a changed
exterior site outside the range-one neighborhood, range one gives equality of full laws. -/
def FarBoundaryEqualityStatement : Prop :=
  ∀ (P : PlaneSpec), RegularSpec P → ∀ a u y, y ∉ square a u →
    setDistance supDist y (↑(square a u) : Set Plane) ≠ 1 →
    ∀ η ξ : Config P.Letter, (∀ z, z ≠ y → η z = ξ z) →
      P.law (square a u) η = P.law (square a u) ξ

/-- `l:hamming`, sec4:291-310. Convert one stopped full-law coupling to a Hamming
bound. The conclusion keeps that same coupling; finite energy is not re-used here. -/
def StoppedHammingConversionStatement : Prop :=
  ∀ (P : PlaneSpec) l p Mstar α n d,
    0 ≤ d → d ≤ p * α^(16*l) → p * α^(16*l) ≤ 1 →
    max Mstar (geometryThreshold l) ≤ n^8 → 4 ≤ n →
    (n : ℝ) ≤ shellSpacing (n^8) → (n : ℝ)*shellSpacing (n^8) = (n : ℝ)^3 →
    StoppedEstimate P l p Mstar α →
    (∀ a y, ((Finset.univ \ farSites a y (n^8) ((n : ℝ)^3)).card : ℝ) ≤ 25*(n : ℝ)^6 ∧
      (Fintype.card (square a (n^8)) : ℝ) ≤ 25*(n : ℝ)^16) →
    (∀ a η, Probability (P.law (square a (n^8)) η)) →
    ∀ a y, setDistance supDist y (↑(square a (n^8)) : Set Plane) = 1 →
    ∀ η ξ : Config P.Letter, (∀ z, z ≠ y → η z = ξ z) →
    ∃ c : Coupling (P.law (square a (n^8)) η) (P.law (square a (n^8)) ξ),
      couplingCost c ≤ 25*(n : ℝ)^6 + 25*(n : ℝ)^16*(1-d)^(n-3)

end AKLT.Blueprint.Gap
