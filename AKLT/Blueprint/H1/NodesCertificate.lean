module
public import AKLT.Blueprint.H1.NodesSector
public import AKLT.Gen.Gram.Theory

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators ComplexOrder
open AKLT.Defs

namespace AKLT.Blueprint.H1

/-- `t:H1`, REV-PLAN lines 2308–2323, and `p:certificate`, Appendix D lines
830–896. REQUIRED EXTERNAL DATA HANDOFF: every covered pattern must actually
have a representation, a group inversion, a justified denominator and passing
Gram witnesses at its exact threshold. Neither existing Top soundness statement
asserts this existence. A data owner should refine this contract into checked
enumeration/orbit coverage and separately kernel-checked certificate shards.
This is not a claim that the study's discarded factors have been recovered. -/
def H1FiniteDataStatementV2 : Prop :=
  ∀ π : PatternData, π.Covered → ∃ r : Representation, ∃ I : Finset (Fin 20),
    GroupInversion π r I ∧ ∃ D₀ : ℕ, ClearsDenominator π r D₀ ∧
      SectorWitnesses π r I D₀ (h1Numerator π) (h1Denominator π)

/-- A concrete V2 handoff if a single certificate interface must imply H1:
include both soundness and actual coverage, not a soundness implication alone. -/
def CertificateStatementV2 : Prop := AKLT.Blueprint.Top.CertificateStatement ∧ H1FiniteDataStatementV2

/-- `l:integercheck`, lines 743–768; an intermediate closed consumer contract
recording the symmetry of the reconstructed threshold matrices. -/
def ThresholdSymmetryStatement : Prop :=
  ∀ π : PatternData, π.Covered → ∀ r : Representation,
    ∀ I : Finset (Fin 20), GroupInversion π r I → ∀ D₀ : ℕ, ClearsDenominator π r D₀ →
    ∀ p q : ℕ, 0 < p → 0 < q → (p : ℚ) / q < 1 → ∀ ε : ExchangeSigns π,
      (thresholdSectorMatrix π r ε I D₀ p q).IsSymm

end AKLT.Blueprint.H1
