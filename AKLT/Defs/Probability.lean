module
public import Mathlib

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators ENNReal

namespace AKLT.Defs

/-- Finite weights. Normalization and positivity are conclusions, never hidden assumptions. -/
abbrev Weight (Ω : Type*) := Ω → ℝ

/-- Normalize a finite weight by its actual partition sum. -/
def normalize {Ω : Type*} [Fintype Ω] (w : Weight Ω) : Weight Ω :=
  fun x => w x / ∑ y, w y

/-- A positive probability on an explicitly finite state space. -/
def PositiveProbability {Ω : Type*} [Fintype Ω] (p : Weight Ω) : Prop :=
  (∀ x, 0 < p x) ∧ ∑ x, p x = 1

/-- An arbitrary finite probability, allowing zero atoms. -/
def Probability {Ω : Type*} [Fintype Ω] (p : Weight Ω) : Prop :=
  (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1

/-- Finite real expectation. -/
def expectation {Ω : Type*} [Fintype Ω] (p : Weight Ω) (f : Ω → ℝ) : ℝ :=
  ∑ x, p x * f x

/-- `d:moment`: total variation with the factor one half. -/
def totalVariation {Ω : Type*} [Fintype Ω] (p q : Weight Ω) : ℝ :=
  (1 / 2) * ∑ x, |p x - q x|

/-- Finite complex expectation. -/
def complexMean {Ω : Type*} [Fintype Ω] (p : Weight Ω) (f : Ω → ℂ) : ℂ :=
  ∑ x, (p x : ℂ) * f x

/-- `d:framemodel`: complex variance, a real nonnegative quadratic form for probabilities. -/
def variance {Ω : Type*} [Fintype Ω] (p : Weight Ω) (f : Ω → ℂ) : ℝ :=
  ∑ x, p x * Complex.normSq (f x - complexMean p f)

/-- Agreement on the complement of a physical block. -/
def AgreeOutside {ι : Type*} {S : ι → Type*} (U : Finset ι)
    (σ τ : (x : ι) → S x) : Prop := ∀ x, x ∉ U → σ x = τ x

/-- `d:framemodel`: conditioning off a block, given by its finite fibre quotient. -/
def conditionalExpectation {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*}
    [∀ x, Fintype (S x)] (p : Weight ((x : ι) → S x)) (U : Finset ι)
    (f : ((x : ι) → S x) → ℂ) (σ : (x : ι) → S x) : ℂ := by
  classical
  exact (∑ τ, if AgreeOutside U σ τ then (p τ : ℂ) * f τ else 0) /
    (∑ τ, if AgreeOutside U σ τ then (p τ : ℂ) else 0)

/-- `d:framemodel`: the pointwise conditional variance E_U |f-E_U f|^2,
with the same explicit fibre denominator as the conditional expectation. -/
def conditionalVariance {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*}
    [∀ x, Fintype (S x)] (p : Weight ((x : ι) → S x)) (U : Finset ι)
    (f : ((x : ι) → S x) → ℂ) (σ : (x : ι) → S x) : ℝ := by
  classical
  exact (∑ τ, if AgreeOutside U σ τ then
    p τ * Complex.normSq (f τ - conditionalExpectation p U f τ) else 0) /
      (∑ τ, if AgreeOutside U σ τ then p τ else 0)

/-- The integrated conditional variance in a physical block. -/
def blockDirichlet {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*}
    [∀ x, Fintype (S x)] (p : Weight ((x : ι) → S x)) (U : Finset ι)
    (f : ((x : ι) → S x) → ℂ) : ℝ :=
  ∑ σ, p σ * Complex.normSq (f σ - conditionalExpectation p U f σ)

/-- `d:framemodel`: rate one per physical site, with no volume normalization. -/
def dirichlet {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*} [∀ x, Fintype (S x)]
    (p : Weight ((x : ι) → S x)) (f : ((x : ι) → S x) → ℂ) : ℝ := by
  classical
  exact ∑ x, blockDirichlet p {x} f

/-- `d:framemodel`: a gap lower bound as a Poincare inequality, including singletons. -/
def PoincareLower {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*} [∀ x, Fintype (S x)]
    (p : Weight ((x : ι) → S x)) (g : ℝ) : Prop :=
  ∀ f, g * variance p f ≤ dirichlet p f

/-- The infimum definition of the heat-bath gap, with infinity for a one-point space. -/
def heatBathGap {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*} [∀ x, Fintype (S x)]
    (p : Weight ((x : ι) → S x)) : ℝ≥0∞ :=
  ⨅ f : {f : ((x : ι) → S x) → ℂ // 0 < variance p f},
    ENNReal.ofReal (dirichlet p f.val / variance p f.val)

/-- `d:moment`: Hamming distance counts actual sites. -/
def hamming {ι : Type*} [Fintype ι] {S : ι → Type*}
    (σ τ : (x : ι) → S x) : ℕ := by
  classical
  exact (Finset.univ.filter fun x => σ x ≠ τ x).card

/-- A finite coupling specified by nonnegative entries and both full marginals. -/
structure Coupling {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
    (p : Weight Ω) (q : Weight Ξ) where
  mass : Ω → Ξ → ℝ
  nonnegative : ∀ x y, 0 ≤ mass x y
  first_marginal : ∀ x, ∑ y, mass x y = p x
  second_marginal : ∀ y, ∑ x, mass x y = q y

end AKLT.Defs
