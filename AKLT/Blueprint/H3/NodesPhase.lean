module
public import AKLT.Blueprint.H3.Basic

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.Blueprint.H3

/-- `l:phase-expansion`, lines 473–506: block-triangular four-phase algebra.
Induct on n, keeping the four row coordinates. A nonzero terminal history has exactly
one A→C or B→D change; zero rewards cause no division or exceptional case. -/
def PhaseFoldExpansionStatement : Prop :=
  ∀ n : ℕ, ∀ k : Fin n → StepKind, ∀ r : Fin n → ℚ,
    (∑ φ : Phase, phaseRun (fun i => phaseTransition (k i) (r i))
      (List.finRange n) phaseInitial φ * phaseTerminal φ) =
    ∑ j : Fin n, (singleChange k r j .A .C + singleChange k r j .B .D)

/-- `l:phase-expansion`, lines 480–505: factor the unique-change products.
Separate revisits (base factor 1/5) from first visits (1/3), then partition earlier/later
straight and turning factors. Each product is finite, including the empty product. -/
def SingleChangeFactorStatement : Prop :=
  ∀ n : ℕ, ∀ w : DirectionWord n, ∀ j : Fin n,
    singleChange (trueKind w) (witnessKappa w) j .A .C +
      singleChange (trueKind w) (witnessKappa w) j .B .D =
    trailBaseWeight kernelStart w * longRewardTerm w j

/-- `l:phase-expansion`, lines 490–508: generic expansion of one finite exposure list.
Induct on a nodup list. The head multiplier and every tail multiplier acquire exactly one
factor; absent indices never enter idxOf. This isolates list algebra from the long-order geometry. -/
def ExposureListExpansionStatement : Prop :=
  ∀ n : ℕ, ∀ w : DirectionWord n, ∀ reward : Fin n → ℚ, ∀ l : List (Fin n), l.Nodup →
    exposureSum w reward l = ∑ j ∈ l.toFinset, reward j * orderedMultiplier w l j

/-- `l:phase-expansion`, lines 490–508: the straight-first list has exactly the first
visits, each once. Its prefix product consists of all earlier straight indices for a straight
response, or all straight and earlier turning indices for a turn. Use finRange order and filter. -/
def LongOrderingMultiplierStatement : Prop :=
  ∀ n : ℕ, ∀ w : DirectionWord n,
    (longOrdering w).Nodup ∧
    (longOrdering w).toFinset = Finset.univ.filter (fun j => wordRevisit kernelStart w j = false) ∧
    ∀ j ∈ longOrdering w, orderedMultiplier w (longOrdering w) j = longMultiplier w j

/-- Derived node for `l:phase-expansion`, lines 490–508: expand the ordered exposure recursion.
Filter finRange into straight and turning first departures, expand by induction on the
lists, and identify each product with longMultiplier. This step is purely finite algebra. -/
def LongExposureExpansionStatement : Prop :=
  ∀ n : ℕ, ∀ w : DirectionWord n,
    exposureSum w (witnessKappa w) (longOrdering w) = ∑ j : Fin n, longRewardTerm w j

/-- `l:phase-expansion`, lines 509–515: causality of true prefix coefficients.
Prefix vertices, incoming directions, departure counts, and dead-neighbor sets agree at
indices below L. The final vertex at L is retained, so the last prefix departure is covered. -/
def PrefixCoefficientCausalityStatement : Prop :=
  ∀ n : ℕ, ∀ w : DirectionWord n, ∀ L : ℕ, ∀ hL : L ≤ n,
    ∀ i : Fin L, ∀ φ ψ : Phase,
      truePhaseCoefficient (takeWord w L) i φ ψ =
        truePhaseCoefficient w ⟨i.val, Nat.lt_of_lt_of_le i.isLt hL⟩ φ ψ

/-- `l:phase-expansion`, lines 509–515: split a finite matrix fold.
The displayed premise is equality of the actual matrices, not another blueprint node.
Use take/drop of finRange and linearity in the initial phase row; no trail assumption is needed. -/
def PhaseSplitAlgebraStatement : Prop :=
  ∀ n : ℕ, ∀ w : DirectionWord n, ∀ L : ℕ, ∀ hL : L ≤ n,
    (∀ i : Fin L, ∀ φ ψ : Phase,
      truePhaseCoefficient (takeWord w L) i φ ψ =
        truePhaseCoefficient w ⟨i.val, Nat.lt_of_lt_of_le i.isLt hL⟩ φ ψ) →
    (∑ φ : Phase, prefixPhases w φ * phaseTerminal φ) =
      ∑ φ : Phase, prefixPhases (takeWord w L) φ * truePhaseSuffix w L φ

/-- The hard exposure step is split into list expansion and long-order prefix products. -/
theorem longExposureExpansion_of_nodes (hList : ExposureListExpansionStatement)
    (hOrder : LongOrderingMultiplierStatement) : LongExposureExpansionStatement := by
  intro n w
  obtain ⟨hn, hf, hm⟩ := hOrder n w
  rw [hList n w (witnessKappa w) (longOrdering w) hn, hf, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : wordRevisit kernelStart w j = false
  · have hmem : j ∈ longOrdering w := by
      apply List.mem_toFinset.mp
      rw [hf]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hj]
    simp only [hj, Bool.false_eq_true, ↓reduceIte, longRewardTerm, hm j hmem]
  · have hj' : wordRevisit kernelStart w j = true := by cases h : wordRevisit kernelStart w j <;> simp_all
    simp [longRewardTerm, hj']

end AKLT.Blueprint.H3
