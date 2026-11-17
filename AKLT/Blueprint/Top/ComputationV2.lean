module
public import AKLT.Blueprint.Top.Computation
public import AKLT.Defs.Automaton10Data

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators ENNReal
open AKLT.Defs

namespace AKLT.Blueprint.Top

/-- `p:automaton10`: the particular supplied map and representatives, not an
existentially unrelated quotient. Raw-code coverage and every representative,
kind/successor/arrival regeneration obligation remain explicit. -/
def Automaton10StatementV2 : Prop :=
  Fintype.card (MemoryWindow 10) = 60092 ∧
  (∀ code : Fin (4^10), Automaton10Data.rawClassAt code.val ≤ 3741 ∧
    (Automaton10Data.rawClassAt code.val < 3741 ↔
      RawWindow (Automaton10Data.decodeWord 10 code.val))) ∧
  (∀ a : Fin 3741, Automaton10Data.representativeCode a < 4^10) ∧
  (∀ a : Fin 3741, ∀ d : Compass,
    Automaton10Data.destinationCode a d ≤ 3741 ∧
    (Automaton10Data.destinationCode a d = 0 ↔ Automaton10Data.kindCode a d = 3) ∧
    (Automaton10Data.destinationCode a d ≠ 0 → Automaton10Data.kindCode a d < 3)) ∧
  Automaton10Data.supplied.Correct ∧
  quotientEdgeCount Automaton10Data.supplied .straight = 2516 ∧
  quotientEdgeCount Automaton10Data.supplied .turn = 5032 ∧
  quotientEdgeCount Automaton10Data.supplied .revisit = 1872

/-- Corrected paper contract; its legacy counterpart remains available
for existing blueprint and prototype proofs. -/
def PhaseExpansionStatementV2 : Prop :=
  ∀ n : ℕ, ∀ X : PairType, ∀ w : DirectionWord n, ClosedTrail X w →
    (∑ φ, prefixPhases w φ * phaseTerminal φ) =
      trailBaseWeight kernelStart w * exposureSum w (witnessKappa w) (longOrdering w) ∧
    ∀ L : ℕ, ∀ hL : L ≤ n,
      let initialWord : DirectionWord L := fun i => w ⟨i.val, Nat.lt_of_lt_of_le i.isLt hL⟩
      (∑ φ, prefixPhases w φ * phaseTerminal φ) =
        ∑ φ, prefixPhases initialWord φ * truePhaseSuffix w L φ

/-- Corrected paper contract; its legacy counterpart remains available
for existing blueprint and prototype proofs. -/
def StationaryDominationStatementV2 : Prop :=
  (∀ Q : MemoryQuotient 10 3741, Q.Correct → ∀ X : PairType, ∀ d₀ : Compass, d₀ ≠ .east →
    ∀ n L : ℕ, 12 ≤ L → L ≤ n → ∀ w : DirectionWord n,
      ClosedTrail X w → SurvivingPrefix X d₀ (takeWord w L) →
      ∀ i : Fin n, L ≤ i.val → ∀ φ ψ : Phase,
        truePhaseCoefficient w i φ ψ ≤ stationaryCoefficientV2 Q X d₀ φ
          (Q.project (lastWindowWord 10 (takeWord w i.val)))
          (wordVertex kernelStart w i.val) (w i) ψ) ∧
  ∀ Q : MemoryQuotient 10 3741, Q.Correct → ∀ X : PairType, ∀ d₀ : Compass, d₀ ≠ .east →
    ∀ L : ℕ, 12 ≤ L → ∀ P : DirectionWord L, SurvivingPrefix X d₀ P → ∀ φ : Phase, ∀ R : ℕ,
      trueContinuationSum X P φ R ≤ stationaryContinuationSumV2 Q X d₀ φ
        (Q.project (lastWindowWord 10 P)) (wordVertex kernelStart P L) R

/-- Corrected paper contract; its legacy counterpart remains available
for existing blueprint and prototype proofs. -/
def StationaryLocalGlobalStatementV2 : Prop :=
  (∀ t : ℚ, 0 ≤ t → t ≤ (coefficientCeiling t : ℚ) / certificateCoefficientScale) ∧
  ∀ Q : MemoryQuotient 10 3741, Q.Correct → ∀ X : PairType, ∀ d₀ : Compass, d₀ ≠ .east →
    ∀ C : StationaryData 3741, C.PassesV2 Q X d₀ →
    (∀ φ a, freeApply Q (fun ψ b => (C.cap ψ b : ℚ) / certificateValueScale) φ a ≤
      (C.cap φ a : ℚ) / certificateValueScale) ∧
    ∀ φ a x, 0 ≤ C.potential φ a x ∧ C.potential φ a x ≤ (C.cap φ a : ℚ) / certificateValueScale ∧
      (x ∉ square (0, 0) certificateRadius → C.potential φ a x = (C.cap φ a : ℚ) / certificateValueScale) ∧
      stationaryReward X φ a x + stationaryApplyV2 Q X d₀ C.potential φ a x ≤ C.potential φ a x ∧
      ∀ R : ℕ, stationaryContinuationSumV2 Q X d₀ φ a x R ≤ C.potential φ a x

/-- Corrected paper contract; its legacy counterpart remains available
for existing blueprint and prototype proofs. -/
def PrefixDominationStatementV2 : Prop :=
  ∀ Q : MemoryQuotient 10 3741, Q.Correct → ∀ X : PairType, ∀ d₀ : Compass, d₀ ≠ .east →
    ∀ C : StationaryData 3741, C.PassesV2 Q X d₀ → ∀ R : ℕ,
      firstDirectionPartialRow X d₀ R ≤ stationaryPrefixBound Q X d₀ C

/-- Corrected paper contract; its legacy counterpart remains available
for existing blueprint and prototype proofs. -/
def StationaryCheckStatementV2 : Prop :=
  (square (0, 0) certificateRadius).card = 19881 ∧
  Automaton10Data.supplied.Correct ∧
    ∃ C : PairType × Compass → StationaryData 3741,
      ∀ k ∈ stationaryCases, (C k).PassesV2 Automaton10Data.supplied k.1 k.2 ∧
        (10^9 : ℚ) * stationaryPrefixBound Automaton10Data.supplied k.1 k.2 (C k) ≤ stationaryPrefixCeiling k.1 k.2

/-- Corrected paper contract; its legacy counterpart remains available
for existing blueprint and prototype proofs. -/
def StationaryAssemblyStatementV2 : Prop :=
  ∀ Q : MemoryQuotient 10 3741, Q.Correct → ∀ C : PairType × Compass → StationaryData 3741,
    (∀ k ∈ stationaryCases, (C k).PassesV2 Q k.1 k.2 ∧
      (10^9 : ℚ) * stationaryPrefixBound Q k.1 k.2 (C k) ≤ stationaryPrefixCeiling k.1 k.2) →
    (∀ R : ℕ, kernelPartialRow .B R ≤
      2 * stationaryPrefixBound Q .B .north (C (.B, .north)) + stationaryPrefixBound Q .B .west (C (.B, .west))) ∧
    (2 * stationaryPrefixBound Q .B .north (C (.B, .north)) + stationaryPrefixBound Q .B .west (C (.B, .west)) ≤
      kernelRho * kernelWitness .B) ∧
    (∀ R : ℕ, kernelPartialRow .C R ≤
      stationaryPrefixBound Q .C .north (C (.C, .north)) + stationaryPrefixBound Q .C .west (C (.C, .west)) +
        stationaryPrefixBound Q .C .south (C (.C, .south))) ∧
    (stationaryPrefixBound Q .C .north (C (.C, .north)) + stationaryPrefixBound Q .C .west (C (.C, .west)) +
      stationaryPrefixBound Q .C .south (C (.C, .south)) ≤ kernelRho * kernelWitness .C) ∧
    (∀ X : PairType, (∑ Y : PairType, shiftedKernel 1 X Y * ENNReal.ofReal (kernelWitness Y : ℝ)) ≤
      ENNReal.ofReal ((kernelRho * kernelWitness X : ℚ) : ℝ)) ∧ H3Statement

end AKLT.Blueprint.Top
