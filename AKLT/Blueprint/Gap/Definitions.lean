import AKLT.Blueprint.Top.Windows

/-! Local vocabulary for the finite, physical-site periodic-gap blueprint.
No field below asserts an unproved global interface result. -/

noncomputable section
set_option maxHeartbeats 800000
open scoped BigOperators
open AKLT.Defs AKLT.Challenge
attribute [local instance] Classical.propDecidable

namespace AKLT.Blueprint.Gap
local instance (α : Type) : DecidableEq α := Classical.decEq α

abbrev Config {ι : Type} (S : ι → Type) := (x : ι) → S x

/-- Restriction to actual sites; dependent alphabets are retained. -/
def restrict {ι : Type} {S : ι → Type} (U : Finset ι) (σ : Config S) :
    (x : U) → S x := fun x => σ x

/-- Agreement on a set of sites of a finite product. -/
def AgreeOn {ι : Type} {S : ι → Type} (U : Finset ι) (σ τ : Config S) : Prop :=
  ∀ x ∈ U, σ x = τ x

/-- Full-state conditional law, supported on the specified exterior fibre. -/
def fibre {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type}
    [∀ x, Fintype (S x)] (p : Weight (Config S)) (U : Finset ι) (σ : Config S) :
    Weight (Config S) := conditionOn p (AgreeOutside U σ)

/-- Conditional law on just the block coordinates. -/
def blockLaw {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type}
    [∀ x, Fintype (S x)] (p : Weight (Config S)) (U : Finset ι) (σ : Config S) :
    Weight ((x : U) → S x) := by
  classical
  exact marginal (fibre p U σ) (restrict U)

/-- Complex weighted scalar product, linear in its second argument. -/
def weightedInner {Ω : Type} [Fintype Ω] (p : Weight Ω) (f h : Ω → ℂ) : ℂ :=
  ∑ σ, (p σ : ℂ) * star (f σ) * h σ

/-- Unnormalised, labelled block Dirichlet form. Repeated blocks count repeatedly. -/
def blockForm {ι J : Type} [Fintype ι] [DecidableEq ι] [Fintype J]
    {S : ι → Type} [∀ x, Fintype (S x)] (p : Weight (Config S))
    (B : J → Finset ι) (f : Config S → ℂ) : ℝ := ∑ a, blockDirichlet p (B a) f

/-- Poincare convention, also meaningful when the configuration space has one point. -/
def BlockGap {ι J : Type} [Fintype ι] [DecidableEq ι] [Fintype J]
    {S : ι → Type} [∀ x, Fintype (S x)] (p : Weight (Config S))
    (B : J → Finset ι) (c : ℝ) : Prop := ∀ f, c * variance p f ≤ blockForm p B f

/-- Mixture of the full-state conditional kernels, one uniform choice per label. -/
def blockAverage {ι J : Type} [Fintype ι] [DecidableEq ι] [Fintype J]
    {S : ι → Type} [∀ x, Fintype (S x)] (p : Weight (Config S))
    (B : J → Finset ι) (σ : Config S) : Weight (Config S) :=
  fun τ => (∑ a, fibre p (B a) σ τ) / Fintype.card J

/-- A real stochastic kernel with detailed balance. -/
def Reversible {Ω : Type} [Fintype Ω] (p : Weight Ω) (K : Ω → Weight Ω) : Prop :=
  (∀ σ, Probability (K σ)) ∧ ∀ σ τ, p σ * K σ τ = p τ * K τ σ

/-- Quadratic form for A(I-K), with A labels and no clock normalisation. -/
def kernelForm {Ω : Type} [Fintype Ω] (p : Weight Ω) (K : Ω → Weight Ω)
    (A : ℝ) (f : Ω → ℂ) : ℝ :=
  A * (weightedInner p f (fun σ => f σ - ∑ τ, (K σ τ : ℂ) * f τ)).re

/-- Maximal one-coordinate oscillation; insert zero so a singleton needs no special max. -/
def lipschitz {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type} [∀ x, Fintype (S x)]
    (f : Config S → ℝ) : ℝ :=
  sSup (insert 0 {r | ∃ σ τ : Config S, hamming σ τ = 1 ∧ r = |f σ - f τ|})

/-- Mean of a real function under one row of a kernel. -/
def kernelMean {Ω : Type} [Fintype Ω] (K : Ω → Weight Ω) (f : Ω → ℝ) : Ω → ℝ :=
  fun σ => expectation (K σ) f

/-- Expected Hamming distance of a coupling of full configuration laws. -/
def couplingCost {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type} [∀ x, Fintype (S x)]
    {p q : Weight (Config S)} (c : Coupling p q) : ℝ :=
  ∑ σ, ∑ τ, c.mass σ τ * (hamming σ τ : ℝ)

/-- Probability of disagreement on specified sites, always in the full-law coupling. -/
def disagreement {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type} [∀ x, Fintype (S x)]
    {p q : Weight (Config S)} (c : Coupling p q) (U : Finset ι) : ℝ := by
  classical
  exact ∑ σ, ∑ τ, if AgreeOn U σ τ then 0 else c.mass σ τ

/-- Finite-energy assignment bound with arbitrary consistent partial conditioning. -/
def AssignmentBound {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type} [∀ x, Fintype (S x)]
    (p : Weight (Config S)) (α : ℝ) : Prop :=
  ∀ U J : Finset ι, Disjoint U J → ∀ a b : Config S,
    α ^ U.card ≤ conditionalProbability p (fun σ => AgreeOn J σ a) (fun σ => AgreeOn U σ b)

/-- A coordinate change includes the precise equality-of-letters correspondence.
It permits permutations of sites and sitewise relabelling, including local antipodes. -/
structure ProductChange {ι κ : Type} (S : ι → Type) (T : κ → Type) where
  sites : ι ≃ κ
  configurations : Config S ≃ Config T
  coordinate_eq : ∀ σ τ x, σ x = τ x ↔ configurations σ (sites x) = configurations τ (sites x)

/-- Finite pushforward equality, not an unnormalised weight comparison. -/
def Carries {ι κ : Type} {S : ι → Type} {T : κ → Type}
    (e : ProductChange S T) (p : Weight (Config S)) (q : Weight (Config T)) : Prop :=
  ∀ σ, q (e.configurations σ) = p σ

/-- An arbitrary finite-alphabet plane specification; total exterior assignments simplify
induced boundaries. Only its finite-volume laws are summed. -/
structure PlaneSpec where
  Letter : Plane → Type
  finite : ∀ x, Fintype (Letter x)
  inhabited : ∀ x, Nonempty (Letter x)
  law : (W : Finset Plane) → Config Letter → Weight ((x : W) → Letter x)

instance (P : PlaneSpec) (x : Plane) : Fintype (P.Letter x) := P.finite x
instance (P : PlaneSpec) (x : Plane) : Nonempty (P.Letter x) := P.inhabited x

abbrev PlaneConfig (P : PlaneSpec) (W : Finset Plane) := (x : W) → P.Letter x

/-- Fill a volume with its sampled letters, keeping the specified exterior. -/
def fill (P : PlaneSpec) (W : Finset Plane) (η : Config P.Letter) (σ : PlaneConfig P W) :
    Config P.Letter := fun x => if hx : x ∈ W then σ ⟨x, hx⟩ else η x

/-- Generic marginal, with exterior values used only if a caller asks outside W. -/
def specMarginal (P : PlaneSpec) (W V : Finset Plane) (η : Config P.Letter) :
    Weight (PlaneConfig P V) := by
  classical
  exact marginal (P.law W η) (fun σ => restrict V (fill P W η σ))

/-- Positivity, full conditioning consistency and range one, without hidden constants. -/
def RegularSpec (P : PlaneSpec) : Prop :=
  (∀ W η, PositiveProbability (P.law W η)) ∧
  (∀ W V, V ⊆ W → ∀ η σ,
    marginal (conditionOn (P.law W η)
      (fun τ => ∀ x : W, x.val ∉ V → τ x = σ x))
      (fun τ => restrict V (fill P W η τ)) = P.law V (fill P W η σ)) ∧
  (∀ (W : Finset Plane) η ξ,
    (∀ x, x ∉ W → setDistance supDist x (↑W : Set Plane) ≤ 1 → η x = ξ x) →
      P.law W η = P.law W ξ)

/-- Uniform finite energy for every finite law in a plane specification. -/
def SpecEnergy (P : PlaneSpec) (α : ℝ) : Prop :=
  ∀ W η, AssignmentBound (P.law W η) α

/-- Generic version of (W), with the same physical sites and all translates. -/
def SpecWindow (P : PlaneSpec) (l : ℕ) (p : ℝ) (Mstar : ℕ) : Prop :=
  1 ≤ l ∧ 1 ≤ Mstar ∧ 0 < p ∧ p ≤ 1 ∧
  ∀ a u, Mstar ≤ u → ∀ y,
    setDistance supDist y (↑(square a u) : Set Plane) = 1 →
    ∀ i : ℤ, 2 ≤ i → (i : ℝ) ≤ shellSpacing u → i ∉ exceptionalIndices a y u →
    ∀ η ξ, totalVariation (specMarginal P (farVolume a y u i) (window a y u l i) η)
      (specMarginal P (farVolume a y u i) (window a y u l i) ξ) ≤ 1 - p

/-- Actual frame family, with total assignments restricted to the finite boundary. -/
def frameSpec (κ : Plane → Fin 3) : PlaneSpec where
  Letter := fun _ => IcoLetter
  finite := fun _ => inferInstance
  inhabited := fun _ => inferInstance
  law := fun W η => planeLaw κ W (fun z => η z)

/-- Local geometric data used at one square; no global Top statement is hidden here. -/
def ShellGeometry (l : ℕ) (a y : Plane) (u : ℕ) : Prop :=
  (exceptionalIndices a y u).card ≤ 1 ∧
  (∀ i : ℤ, 2 ≤ i → i ≤ lastShellIndex u → shell a y u i ⊆ farVolume a y u i) ∧
  (∀ i : ℤ, 2 ≤ i → i ≤ lastShellIndex u → i ∉ exceptionalIndices a y u →
    (nearShell a y u l i).card ≤ 8 * l) ∧
  ∀ i : ℤ, 2 ≤ i →
    (∀ x ∈ square a u \ farVolume a y u i,
      setDistance supDist x (↑(farVolume a y u i) : Set Plane) ≤ 1 → x ∈ shell a y u (i - 1)) ∧
    ¬ setDistance supDist y (↑(farVolume a y u i) : Set Plane) ≤ 1

/-- Trial indices whose successor surgery is also unskipped. -/
def trials (a y : Plane) (u h : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 2 h).filter fun i => (i : ℤ) ∉ exceptionalIndices a y u ∧
    (i + 1 : ℤ) ∉ exceptionalIndices a y u

/-- Target far region, indexed as sites of the full square. -/
def farSites (a y : Plane) (u : ℕ) (r : ℝ) : Finset (square a u) := by
  classical
  exact Finset.univ.filter fun x => r < (supDist x.val y : ℝ)

/-- A finite path of pairs, with step i acting from time i to time i+1. -/
abbrev PairTrace (Ω : Type) (m : ℕ) := Fin (m + 1) → Ω × Ω

/-- Distribution of a time-inhomogeneous finite chain of configuration pairs. -/
def traceLaw {Ω : Type} [Fintype Ω] (m : ℕ) (initial : Weight (Ω × Ω))
    (K : Fin m → Ω × Ω → Weight (Ω × Ω)) : Weight (PairTrace Ω m) :=
  fun t => initial (t 0) * ∏ j : Fin m, K j (t j.castSucc) (t j.succ)

/-- Stochastic, pair-dependent surgery kernels with correct conditional full marginals. -/
structure SurgeryKernels (P : PlaneSpec) (a y : Plane) (u l h : ℕ)
    (p α : ℝ) (η ξ : Config P.Letter) where
  kernel : Fin h → (PlaneConfig P (square a u) × PlaneConfig P (square a u)) →
    Weight (PlaneConfig P (square a u) × PlaneConfig P (square a u))
  stochastic : ∀ j ω, Probability (kernel j ω)
  marginals : ∀ j ω,
    if (j.val + 2 : ℤ) ∈ exceptionalIndices a y u then
      ∀ v, kernel j ω v = if v = ω then 1 else 0
    else
      (∀ σ, ∑ τ, kernel j ω (σ, τ) =
        fibre (P.law (square a u) η) (sitesInVolume (square a u) (farVolume a y u (j.val + 2))) ω.1 σ) ∧
      (∀ τ, ∑ σ, kernel j ω (σ, τ) =
        fibre (P.law (square a u) ξ) (sitesInVolume (square a u) (farVolume a y u (j.val + 2))) ω.2 τ)
  fixed_exterior : ∀ j ω v, 0 < kernel j ω v →
    AgreeOutside (sitesInVolume (square a u) (farVolume a y u (j.val + 2))) ω.1 v.1 ∧
    AgreeOutside (sitesInVolume (square a u) (farVolume a y u (j.val + 2))) ω.2 v.2
  identical : ∀ j ω, (j.val + 2 : ℤ) ∉ exceptionalIndices a y u →
    AgreeOn (sitesInVolume (square a u) (shell a y u (j.val + 1))) ω.1 ω.2 →
    ∀ v, 0 < kernel j ω v →
      AgreeOn (sitesInVolume (square a u) (farVolume a y u (j.val + 2))) v.1 v.2
  success : ∀ j ω, j.val + 2 ≤ h → (j.val + 2 : ℤ) ∉ exceptionalIndices a y u →
    p * α ^ (16 * l) ≤ eventMass (kernel j ω)
      (fun v => AgreeOn (sitesInVolume (square a u) (shell a y u (j.val + 2))) v.1 v.2)

/-- A coordinate reduction; there is no global parity sign on this torus. -/
def reduction (L N : Size) (z : Plane) : Site L N := (z.1, z.2)

/-- Labelled torus square and its full sup-distance-one halo. -/
def torusSquare (L N : Size) (M : ℕ) (a : Site L N) : Finset (Site L N) :=
  (square (0, 0) M).image fun z => a + reduction L N z

def torusHalo (L N : Size) (M : ℕ) (a : Site L N) : Finset (Site L N) :=
  torusSquare L N (M + 1) a

def volumeCount (M : ℕ) : ℕ := (2 * M + 1)^2
def haloCount (M : ℕ) : ℕ := 8 * M + 8
def internalCount (M : ℕ) : ℕ := 2 * (2 * M + 1) * (2 * M)
def blockGapConstant (M : ℕ) : ℝ := frameRatio ^ internalCount M

/-- Explicit all-parity cycle colour, with a third colour at the last odd site. -/
def cycleColour (m i : ℕ) : ℕ := if Odd m ∧ i = m - 1 then 2 else i % 2

def torusColour (L N : Size) (x : Site L N) : Fin 3 :=
  ⟨(cycleColour L.val x.1.val + cycleColour N.val x.2.val) % 3, Nat.mod_lt _ (by decide)⟩

/-- Markov dependence relative to the full physical halo (corner sites included). -/
def TorusRangeOne {L N : Size} {S : Site L N → Type} [∀ x, Fintype (S x)]
    (p : Weight (Config S)) (M : ℕ) : Prop :=
  ∀ a σ τ, AgreeOn (torusHalo L N M a \ torusSquare L N M a) σ τ →
    blockLaw p (torusSquare L N M a) σ = blockLaw p (torusSquare L N M a) τ

def UniformBlockGap {L N : Size} {S : Site L N → Type} [∀ x, Fintype (S x)]
    (p : Weight (Config S)) (M : ℕ) (g : ℝ) : Prop :=
  ∀ a σ, PoincareLower (blockLaw p (torusSquare L N M a) σ) g

def BlockInfluence {L N : Size} {S : Site L N → Type} [∀ x, Fintype (S x)]
    (p : Weight (Config S)) (M : ℕ) (K : ℝ) : Prop :=
  ∀ a y, y ∈ torusHalo L N M a \ torusSquare L N M a → ∀ σ τ,
    AgreeOutside {y} σ τ → ∃ c : Coupling (blockLaw p (torusSquare L N M a) σ)
      (blockLaw p (torusSquare L N M a) τ),
      couplingCost (ι := torusSquare L N M a) (S := fun x => S x.val) c ≤ K

/-- The exact three counts used in the periodic argument; sums are over labels. -/
def PeriodicCounts (L N : Size) (M : ℕ) : Prop :=
  (∀ x, (Finset.univ.filter fun a => x ∈ torusSquare L N M a).card = volumeCount M) ∧
  (∀ x, (Finset.univ.filter fun a => x ∈ torusHalo L N M a \ torusSquare L N M a).card = haloCount M) ∧
  volumeCount M ≤ Fintype.card (Site L N)

/-- One local gauge, common to all exterior fibres of a labelled block. -/
structure BoxGauge (L N : Size) (M : ℕ) (a : Site L N) (κ : Site L N → Fin 3) where
  centre : Plane
  centre_reduces : reduction L N centre = a
  change : ProductChange (fun _ : torusSquare L N M a => IcoLetter)
    (fun _ : square centre M => IcoLetter)
  boundary : TorusConfiguration L N → Config (fun _ : Plane => IcoLetter)
  carries : ∀ σ, Carries change (blockLaw (torusLaw L N κ) (torusSquare L N M a) σ)
    ((frameSpec (κ ∘ reduction L N)).law (square centre M) (boundary σ))
  boundary_change : ∀ y, y ∈ torusHalo L N M a \ torusSquare L N M a →
    ∀ σ τ, AgreeOutside {y} σ τ → ∃ z : Plane,
      z ∉ square centre M ∧ setDistance supDist z (↑(square centre M) : Set Plane) = 1 ∧
      ∀ w, w ≠ z → boundary σ w = boundary τ w

/-- The four explicit scale inequalities in l:hamming, chosen before torus periods. -/
def ScaleConditions (l Mstar : ℕ) (d : ℝ) (n : ℕ) : Prop :=
  44 ≤ n ∧ Mstar ≤ n^8 ∧ max 50000 (6 * (l + 1)) ≤ n^2 ∧
    (50000 : ℝ) * 2^20 * (Nat.factorial 20 : ℝ) ≤ (n : ℝ)^12 * d^20

/-- Local row certificate, including the skipped identity row. -/
def RowConditions (P : PlaneSpec) (a y : Plane) (u l h : ℕ) (p α : ℝ)
    (η ξ : Config P.Letter) (j : Fin h)
    (ω : PlaneConfig P (square a u) × PlaneConfig P (square a u))
    (r : Weight (PlaneConfig P (square a u) × PlaneConfig P (square a u))) : Prop :=
  Probability r ∧
  (if (j.val + 2 : ℤ) ∈ exceptionalIndices a y u then
    ∀ v, r v = if v = ω then 1 else 0
  else
    (∀ σ, ∑ τ, r (σ, τ) = fibre (P.law (square a u) η)
      (sitesInVolume (square a u) (farVolume a y u (j.val + 2))) ω.1 σ) ∧
    (∀ τ, ∑ σ, r (σ, τ) = fibre (P.law (square a u) ξ)
      (sitesInVolume (square a u) (farVolume a y u (j.val + 2))) ω.2 τ)) ∧
  (∀ v, 0 < r v →
    AgreeOutside (sitesInVolume (square a u) (farVolume a y u (j.val + 2))) ω.1 v.1 ∧
    AgreeOutside (sitesInVolume (square a u) (farVolume a y u (j.val + 2))) ω.2 v.2) ∧
  ((j.val + 2 : ℤ) ∉ exceptionalIndices a y u →
    AgreeOn (sitesInVolume (square a u) (shell a y u (j.val + 1))) ω.1 ω.2 →
    ∀ v, 0 < r v → AgreeOn (sitesInVolume (square a u) (farVolume a y u (j.val + 2))) v.1 v.2) ∧
  (j.val + 2 ≤ h → (j.val + 2 : ℤ) ∉ exceptionalIndices a y u →
    p * α ^ (16 * l) ≤ eventMass r
      (fun v => AgreeOn (sitesInVolume (square a u) (shell a y u (j.val + 2))) v.1 v.2))

def independentPairs {Ω : Type} (p q : Weight Ω) : Weight (Ω × Ω) := fun ω => p ω.1 * q ω.2

def surgeryTrace (P : PlaneSpec) (a y : Plane) (u l h : ℕ) (p α : ℝ)
    (η ξ : Config P.Letter) (R : SurgeryKernels P a y u l h p α η ξ) :
    Weight (PairTrace (PlaneConfig P (square a u)) h) :=
  traceLaw h (independentPairs (P.law (square a u) η) (P.law (square a u) ξ)) R.kernel

def trialTimes (a y : Plane) (u h : ℕ) : Finset (Fin h) :=
  Finset.univ.filter fun j => j.val + 2 ≤ h ∧ (j.val + 2 : ℤ) ∉ exceptionalIndices a y u ∧
    (j.val + 3 : ℤ) ∉ exceptionalIndices a y u

def shellAgreement (P : PlaneSpec) (a y : Plane) (u h : ℕ) (j : Fin h)
    (ω : PlaneConfig P (square a u) × PlaneConfig P (square a u)) : Prop :=
  AgreeOn (sitesInVolume (square a u) (shell a y u (j.val + 2))) ω.1 ω.2

/-- Result interface for stopped coupling, with fixed l,p,Mstar,alpha. -/
def StoppedEstimate (P : PlaneSpec) (l : ℕ) (p : ℝ) (Mstar : ℕ) (α : ℝ) : Prop :=
  ∀ a u, max Mstar (geometryThreshold l) ≤ u → ∀ y,
    setDistance supDist y (↑(square a u) : Set Plane) = 1 →
    ∀ η ξ : Config P.Letter, (∀ z, z ≠ y → η z = ξ z) →
    ∀ h : ℕ, 4 ≤ h → (h : ℝ) ≤ shellSpacing u →
    ∃ c : Coupling (P.law (square a u) η) (P.law (square a u) ξ),
      disagreement c (farSites a y u ((h : ℝ) * shellSpacing u)) ≤ (1 - p * α^(16*l))^(h-3)

/-- A single scale chosen uniformly over translates and all exterior fibres. -/
def HammingEstimate (P : PlaneSpec) (M : ℕ) (K : ℝ) : Prop :=
  ∀ a y, y ∉ square a M → ∀ η ξ : Config P.Letter,
    (∀ z, z ≠ y → η z = ξ z) →
    ∃ c : Coupling (P.law (square a M) η) (P.law (square a M) ξ), couplingCost c ≤ K

end AKLT.Blueprint.Gap
