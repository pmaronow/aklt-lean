module
public import AKLT.Cert.H1.Production.Semantics

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

namespace AKLT.Cert.H1.Production.TopLeaves
open AKLT.Defs
open scoped BigOperators ComplexOrder
noncomputable section
def integerEntries : Prop :=
  ∀ π : PatternData, π.Covered → ∀ r : Representation,
  ∀ I : Finset (Fin 20), GroupInversion π r I →
  ∀ D₀ : ℕ, ClearsDenominator π r D₀ → ∀ ε : ExchangeSigns π,
  ∀ next : Bool, (integerSectorMatrix π r ε I D₀ next).IsSymm ∧
    ∀ a b, (integerSectorMatrix π r ε I D₀ next a b : ℚ) =
      (if next then 5 else 3) * (D₀ : ℚ) * rationalSectorEntry π r ε
        (invertPolynomial I (reducedPolynomial π r next)) a b

/-- Identification with the complex Pauli form at the exact positive scale. -/
def thresholdScale : Prop :=
  ∀ π : PatternData, π.Covered → ∀ r : Representation,
  ∀ I : Finset (Fin 20), GroupInversion π r I →
  ∀ D₀ : ℕ, ClearsDenominator π r D₀ →
  ∀ p q : ℕ, 0 < p → 0 < q → (p : ℚ) / q < 1 →
  ∀ ε : ExchangeSigns π, ∀ a b,
    (thresholdSectorMatrix π r ε I D₀ p q a b : ℂ) =
      (15 * (D₀ : ℂ) * q) * complexSectorMatrix π r ε
        (invertPolynomial I (reducedDifference π r ((p : ℚ) / q))) a b

/-- Positive congruence scaling, in the exact form requested by IntegerCheck. -/
def positiveScale : Prop :=
  ∀ π : PatternData, π.Covered → ∀ r : Representation,
  ∀ I : Finset (Fin 20), GroupInversion π r I →
  ∀ D₀ : ℕ, ClearsDenominator π r D₀ →
  ∀ p q : ℕ, 0 < p → 0 < q → (p : ℚ) / q < 1 →
  ∀ ε : ExchangeSigns π,
    (complexSectorMatrix π r ε
      (invertPolynomial I (reducedDifference π r ((p : ℚ) / q)))).PosDef ↔
      ((thresholdSectorMatrix π r ε I D₀ p q).map (Int.castRingHom ℂ)).PosDef

/-- The optional Sylvester criterion is a separate universal mathematical leaf. -/
def sylvester : Prop :=
  ∀ n : ℕ, ∀ M : Matrix (Fin n) (Fin n) ℤ, M.IsSymm →
    ((M.map (Int.castRingHom ℝ)).PosDef ↔
      ∀ k : ℕ, ∀ h : k ≤ n, 0 < k → 0 < leadingMinor M k h)

/-- Bareiss pivot/minor identity and exact divisibility, including zero-pivot guard. -/
def bareiss : Prop :=
  ∀ n : ℕ, ∀ M : Matrix (Fin n) (Fin n) ℤ, M.IsSymm →
  ∀ j : ℕ, ∀ h : j < n, (∀ k < j, bareissPivot M k ≠ 0) →
    bareissPivot M j = leadingMinor M (j+1) (Nat.succ_le_of_lt h) ∧
    ∀ i l : Fin n, j < i.val → j < l.val →
      (bareissState M j).2 ∣
        (bareissPivot M j * (bareissState M j).1 i l -
          (bareissState M j).1 i ⟨j,h⟩ * (bareissState M j).1 ⟨j,h⟩ l)

/-- Analytic reduction after positivity of the actual indexed integer sectors.
This omits Gram data: the assembly supplies positivity using the proved Gen library. -/
def sectorPositiveImpliesBound : Prop :=
  ∀ π : PatternData, π.Covered → ∀ r : Representation,
  ∀ I : Finset (Fin 20), GroupInversion π r I →
  ∀ D₀ : ℕ, ClearsDenominator π r D₀ →
  ∀ p q : ℕ, 0 < p → 0 < q → (p : ℚ) / q < 1 →
    (∀ ε : ExchangeSigns π, ∃ t : ℕ, ∃ index : Fin t ≃ CentralBasis π r ε,
      ((indexedSectorMatrix π r ε I D₀ p q index).map (Int.castRingHom ℂ)).PosDef) →
    ∀ m : Fin 20 → UnitVector,
      0 ≤ patternCurrent π m - ((p : ℝ) / q) * patternNext π m

def integerCheckPremises : Prop :=
  integerEntries ∧ thresholdScale ∧ positiveScale ∧ sylvester ∧ bareiss

def certificatePremises : Prop := integerEntries ∧ sectorPositiveImpliesBound

end
end AKLT.Cert.H1.Production.TopLeaves
