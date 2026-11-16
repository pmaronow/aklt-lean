import AKLT.Blueprint.H1.NodesStructure

noncomputable section
open scoped BigOperators ComplexOrder
open AKLT.Defs

namespace AKLT.Blueprint.H1

/-- `d:exchange`, lines 467–498; verify the local single, symmetric-pair, and
exterior-pair ladder actions and then the product rule. This statement deliberately
does not require coveredness: the defined groups always give disjoint tokens. -/
def SectorSpinStableStatement : Prop :=
  ∀ π : PatternData, ∀ r : Representation, ∀ ε : ExchangeSigns π,
    SpinStable (reductionVectors π r) (exchangeSpace π r ε)

/-- `d:exchange`, lines 467–494; each explicit integer-coordinate tensor vector
is an S_z eigenvector. Single weights have parity fixed by their number; symmetric
pair weights are integral and exterior weights are zero. -/
def SectorWeightBasisStatement : Prop :=
  ∀ π : PatternData, ∀ r : Representation, ∀ ε : ExchangeSigns π,
    ∀ b : ExchangeBasis π r ε,
      totalSpinZ (reductionVectors π r) (sectorVector π r ε b) =
        (exchangeWeight π r ε b : ℂ) • sectorVector π r ε b ∧
      ∃ z : ℤ, (exchangeWeight π r ε b : ℝ) = (centralWeight π r : ℝ) + z

/-- `l:sector`, lines 515–520; a nonzero eigenvector in the span of a finite
weight basis has one of its weights. Independence and normalization of the
spanning family are unnecessary. Use the direct sum of distinct eigenspaces. -/
def SpanWeightLatticeStatement : Prop :=
  ∀ J : Finset (Fin 20), ∀ (β : Type) [Fintype β],
    ∀ v : β → TensorSpace J, ∀ w : β → ℝ, ∀ κ : ℝ,
      (∀ b, totalSpinZ J (v b) = (w b : ℂ) • v b) →
      (∀ b, ∃ z : ℤ, w b = κ + z) →
      ∀ ψ ∈ Submodule.span ℂ (Set.range v), ψ ≠ 0 → ∀ m : ℝ,
        totalSpinZ J ψ = (m : ℂ) • ψ → ∃ z : ℤ, m = κ + z

/-- `d:exchange`, lines 494–499; token lifts preserve adjoints and distinct
token operators commute. Verify the 2×2 adjoint identities first. -/
def SpinAdjointStatement : Prop :=
  ∀ J : Finset (Fin 20), ∀ ψ χ : TensorSpace J,
    inner ℂ (totalSpinZ J ψ) χ = inner ℂ ψ (totalSpinZ J χ) ∧
    inner ℂ (totalSpinPlus J ψ) χ = inner ℂ ψ (totalSpinMinus J χ)

/-- `d:exchange`, lines 494–499; token lifts of distinct factors commute, so
the local sl2 identities sum to these three global commutators. -/
def SpinCommutatorStatement : Prop :=
  ∀ J : Finset (Fin 20), ∀ ψ : TensorSpace J,
    totalSpinZ J (totalSpinPlus J ψ) - totalSpinPlus J (totalSpinZ J ψ) = totalSpinPlus J ψ ∧
    totalSpinZ J (totalSpinMinus J ψ) - totalSpinMinus J (totalSpinZ J ψ) = -totalSpinMinus J ψ ∧
    totalSpinPlus J (totalSpinMinus J ψ) - totalSpinMinus J (totalSpinPlus J ψ) =
      (2 : ℂ) • totalSpinZ J ψ

/-- `l:sector`, lines 522–533; combine adjoints and commutators to obtain
||S_-v||²-||S_+v||²=2m||v||² and the shifted weights. Norm positivity proves
nonvanishing; zero vectors are excluded only for that conclusion. -/
def WeightLadderTransferStatement : Prop :=
  ∀ J : Finset (Fin 20),
    (∀ ψ χ : TensorSpace J,
      inner ℂ (totalSpinZ J ψ) χ = inner ℂ ψ (totalSpinZ J χ) ∧
      inner ℂ (totalSpinPlus J ψ) χ = inner ℂ ψ (totalSpinMinus J χ)) →
    (∀ ψ : TensorSpace J,
      totalSpinZ J (totalSpinPlus J ψ) - totalSpinPlus J (totalSpinZ J ψ) = totalSpinPlus J ψ ∧
      totalSpinZ J (totalSpinMinus J ψ) - totalSpinMinus J (totalSpinZ J ψ) = -totalSpinMinus J ψ ∧
      totalSpinPlus J (totalSpinMinus J ψ) - totalSpinMinus J (totalSpinPlus J ψ) =
        (2 : ℂ) • totalSpinZ J ψ) → WeightLadder J

/-- `l:sector`, lines 511–520; restrict the Hermitian Z to the nonzero O
eigenspace inside S and apply its finite-dimensional spectral theorem. Its
eigenvalue m is real. All invariance and inherited-inner-product premises are explicit. -/
def CommonWeightEigenvectorStatement : Prop :=
  ∀ J : Finset (Fin 20), ∀ S : Submodule ℂ (TensorSpace J),
    ∀ O : Module.End ℂ (TensorSpace J), (∀ ψ ∈ S, O ψ ∈ S) →
      (∀ ψ ∈ S, ∀ χ ∈ S, inner ℂ (O ψ) χ = inner ℂ ψ (O χ)) →
      (∀ ψ ∈ S, totalSpinZ J ψ ∈ S) →
      (∀ ψ ∈ S, ∀ χ ∈ S, inner ℂ (totalSpinZ J ψ) χ = inner ℂ ψ (totalSpinZ J χ)) →
      (∀ ψ ∈ S, O (totalSpinZ J ψ) = totalSpinZ J (O ψ)) →
      ∀ μ ∈ eigenvaluesOn S O, ∃ v ∈ S, v ≠ 0 ∧ O v = μ • v ∧
        ∃ m : ℝ, totalSpinZ J v = (m : ℂ) • v

/-- `l:sector`, lines 535–549; induct on the integer distance z to κ using
S_- for positive z and S_+ for negative z. Every intermediate step has the
strict sign required by nonvanishing. No natural-number subtraction is used. -/
def LadderWalkStatement : Prop :=
  ∀ J : Finset (Fin 20), ∀ S : Submodule ℂ (TensorSpace J), ∀ κ : ℝ,
    (κ = 0 ∨ κ = 1 / 2) → SpinStable J S → WeightLadder J →
    ∀ O : Module.End ℂ (TensorSpace J),
      (∀ ψ ∈ S, O (totalSpinPlus J ψ) = totalSpinPlus J (O ψ)) →
      (∀ ψ ∈ S, O (totalSpinMinus J ψ) = totalSpinMinus J (O ψ)) →
      ∀ μ : ℂ, ∀ v ∈ S, v ≠ 0 → O v = μ • v → ∀ m : ℝ,
      totalSpinZ J v = (m : ℂ) • v → (∃ z : ℤ, m = κ + z) →
      ∃ w ∈ S, w ≠ 0 ∧ O w = μ • w ∧ totalSpinZ J w = (κ : ℂ) • w

/-- `l:sector`, lines 551–555; the spectral theorem on the invariant subspace
equates strict quadratic-form positivity with positivity of all eigenvalues.
The zero-dimensional subspace satisfies both sides vacuously. -/
def PositiveSpectrumStatement : Prop :=
  ∀ J : Finset (Fin 20), ∀ S : Submodule ℂ (TensorSpace J),
    ∀ O : Module.End ℂ (TensorSpace J), (∀ ψ ∈ S, O ψ ∈ S) →
      (∀ ψ ∈ S, ∀ χ ∈ S, inner ℂ (O ψ) χ = inner ℂ ψ (O χ)) →
      (PositiveOn S O ↔ ∀ μ ∈ eigenvaluesOn S O, 0 < μ.re)

/-- The central weight has exactly the two values used in the ladder walk. -/
def CentralWeightHalfStatement : Prop :=
  ∀ π : PatternData, ∀ r : Representation,
    (centralWeight π r : ℝ) = 0 ∨ (centralWeight π r : ℝ) = 1 / 2

theorem centralWeightHalf : CentralWeightHalfStatement := by
  intro π r
  unfold centralWeight
  split <;> norm_num

end AKLT.Blueprint.H1
