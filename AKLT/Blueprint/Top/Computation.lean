module
public import AKLT.Blueprint.Top.Coefficients
public import AKLT.Defs.Computational

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators ENNReal
open AKLT.Defs

namespace AKLT.Blueprint.Top

/-- `l:alm`: true window-mass domination and the exact finite base-constant implication. -/
def ALMStatement : Prop :=
  ∀ m : ℕ, 1 ≤ m →
    (∀ n : ℕ, m ≤ n → ∀ u : Plane, ∀ incoming : Compass, ∀ ω' : MemoryWindow m,
      memoryTrailMass m (n + 1) u incoming ω' ≤
        ∑ ω : MemoryWindow m, memoryTrailMass m n u incoming ω * memoryMatrix m ω ω') ∧
    ∀ v : MemoryWindow m → ℝ, (∀ ω, 0 < v ω) → ∀ q : ℝ, 0 < q → q < 1 →
      (∀ ω, (∑ ω', (memoryMatrix m ω ω' : ℝ) * v ω') ≤ q * v ω) →
      OpenTrailBound (memoryBaseConstant m q v) q ∧
      ∀ CV : ℝ, memoryBaseConstant m q v ≤ CV → OpenTrailBound CV q

/-- `l:H2-dihedral`: raw symmetry, exact representative coverage, and counts,
and soundness of checking only one representative of each orbit. -/
def H2DihedralStatement : Prop :=
  (∀ m : ℕ, 1 ≤ m → ∀ g : SquareSymmetry, ∀ w : DirectionWord m, RawWindow w →
    RawWindow (symmetryWord g w) ∧ ∀ d : Compass,
      (WindowAdmissible (symmetryWord g w) (symmetryDirection g d) ↔ WindowAdmissible w d) ∧
      windowKind (symmetryWord g w) (symmetryDirection g d) = windowKind w d ∧
      windowSuccessor (symmetryWord g w) (symmetryDirection g d) = symmetryWord g (windowSuccessor w d)) ∧
  Fintype.card (MemoryWindow 6) = 916 ∧
  ∃ reps : Fin 115 → MemoryWindow 6, Function.Injective reps ∧
    (∀ w : MemoryWindow 6, ∃! j : Fin 115, SameWindowOrbit w.val (reps j).val) ∧
    ∀ v : MemoryWindow 6 → ℝ,
      (∀ ω, 0 < v ω) → (∀ ω ω', SameWindowOrbit ω.val ω'.val → v ω = v ω') →
      ∀ q : ℝ, (∀ j, (∑ ω', (memoryMatrix 6 (reps j) ω' : ℝ) * v ω') ≤ q * v (reps j)) →
        ∀ ω, (∑ ω', (memoryMatrix 6 ω ω' : ℝ) * v ω') ≤ q * v ω

/-- `p:H2-test`: a positive integer orbit-constant witness, exact extrema and maximum
row ratio, regenerated rational weights, and the denominator-cleared integer row test. -/
def H2TestStatement : Prop :=
  (2695605 : ℚ) * kindWeight .straight = 935000 ∧
  (2695605 : ℚ) * kindWeight .turn = 961000 ∧
  (2695605 : ℚ) * kindWeight .revisit = 539121 ∧
  ∃ v : MemoryWindow 6 → ℤ, ∃ lo hi : ℤ,
    0 < lo ∧ (∀ ω, lo ≤ v ω ∧ v ω ≤ hi) ∧ (∃ ω, v ω = lo) ∧ (∃ ω, v ω = hi) ∧
    (hi : ℚ) / lo = 250000000000 / 46594269069 ∧ (hi : ℚ) / lo < 6 ∧
    (∀ ω ω', SameWindowOrbit ω.val ω'.val → v ω = v ω') ∧
    (∀ ω, (∑ ω', memoryMatrix 6 ω ω' * (v ω' : ℚ)) / (v ω : ℚ) ≤ certifiedRate) ∧
    (∃ ω, (∑ ω', memoryMatrix 6 ω ω' * (v ω' : ℚ)) / (v ω : ℚ) = certifiedRate) ∧
    (∀ ω, (1120437614225 : ℤ) *
      (∑ ω', ⌊(2695605 : ℚ) * memoryMatrix 6 ω ω'⌋ * v ω') ≤
        1119948287353 * 2695605 * v ω) ∧ certifiedRate < (2499 / 2500 : ℚ)

/-- `l:H2-CV`: exact base-sum majorant and C_V=10 consequence for the selected witness. -/
def H2CVStatement : Prop :=
  (∀ u : Plane, ∀ incoming : Compass, ∀ r : ℕ, r ≤ 6 →
    openTrailTotal r u incoming ≤ passageFactor false ^ r) ∧
  (6 * (200 / (187 * certifiedRate))^6 < (10 : ℚ)) ∧
  (∀ v : MemoryWindow 6 → ℝ, (∀ ω, 0 < v ω) → memoryWitnessRatio v ≤ 6 →
    memoryBaseConstant 6 (certifiedRate : ℝ) v ≤ 6 * (200 / (187 * (certifiedRate : ℝ)))^6 ∧
    memoryBaseConstant 6 (certifiedRate : ℝ) v < 10) ∧
  (H2TestStatement → H2Statement)

/-- `l:automaton-quotient`: raw and quotient backward operators intertwine, as do
all finite stopped iterates. Revisit coefficients are independent of final direction. -/
def AutomatonQuotientStatement : Prop :=
  (∀ m q : ℕ, 1 ≤ m → ∀ π : DirectionWord m → Fin q, CompatibleProjection m q π →
    ∃ Q : MemoryQuotient m q, Q.Correct ∧ ∀ w, RawWindow w → Q.project w = π w) ∧
  ∀ m q : ℕ, 1 ≤ m → ∀ Q : MemoryQuotient m q, Q.Correct →
    (∀ w : DirectionWord m, RawWindow w → ∀ d : Compass, WindowAdmissible w d →
      RawWindow (windowSuccessor w d)) ∧
    ∀ p : ℕ, ∀ weight : Fin p → Fin p → StepKind → Compass → Compass → Plane → ℚ,
      (∀ φ ψ d a a' x, weight φ ψ .revisit d a x = weight φ ψ .revisit d a' x) →
      ∀ terminal : Plane → Bool, ∀ G : Fin p → Fin q → Plane → ℚ,
      ∀ R : ℕ, ∀ φ : Fin p, ∀ w : DirectionWord m, RawWindow w → ∀ x : Plane,
        ((rawBackward m p weight terminal)^[R]) (fun ψ ω y => G ψ (Q.project ω) y) φ w x =
          ((quotientBackward Q p weight terminal)^[R]) G φ (Q.project w) x

/-- Legacy existential quotient assertion, retained for existing H3 proofs.
`Automaton10StatementV2` binds the designated supplied archive. -/
def Automaton10Statement : Prop :=
  Fintype.card (MemoryWindow 10) = 60092 ∧
  ∃ Q : MemoryQuotient 10 3741, Q.Correct ∧
    quotientEdgeCount Q .straight = 2516 ∧ quotientEdgeCount Q .turn = 5032 ∧
    quotientEdgeCount Q .revisit = 1872

/-- Legacy general phase algebra on all trails; the published closed-trail
scope is `PhaseExpansionStatementV2`. The long-order reward is the sum over the actual
phase histories; the suffix fold retains the precise split at every prefix length. -/
def PhaseExpansionStatement : Prop :=
  ∀ n : ℕ, ∀ w : DirectionWord n, IsTrail kernelStart kernelIncoming w →
    (∑ φ, prefixPhases w φ * phaseTerminal φ) =
      trailBaseWeight kernelStart w * exposureSum w (witnessKappa w) (longOrdering w) ∧
    ∀ L : ℕ, ∀ hL : L ≤ n,
      let initialWord : DirectionWord L := fun i => w ⟨i.val, Nat.lt_of_lt_of_le i.isLt hL⟩
      (∑ φ, prefixPhases w φ * phaseTerminal φ) =
        ∑ φ, prefixPhases initialWord φ * truePhaseSuffix w L φ

/-- `l:stationary-domination`: every true continuation, with any prefix phase,
is dominated at every finite suffix horizon. The indispensable L>=m+2 is explicit. -/
def StationaryDominationStatement : Prop :=
  (∀ Q : MemoryQuotient 10 3741, Q.Correct → ∀ X : PairType, ∀ d₀ : Compass, d₀ ≠ .east →
    ∀ n L : ℕ, 12 ≤ L → L ≤ n → ∀ w : DirectionWord n,
      ClosedTrail X w → SurvivingPrefix X d₀ (takeWord w L) →
      ∀ i : Fin n, L ≤ i.val → ∀ φ ψ : Phase,
        truePhaseCoefficient w i φ ψ ≤ stationaryCoefficient Q X d₀ φ
          (Q.project (lastWindowWord 10 (takeWord w i.val)))
          (wordVertex kernelStart w i.val) (w i) ψ) ∧
  ∀ Q : MemoryQuotient 10 3741, Q.Correct → ∀ X : PairType, ∀ d₀ : Compass, d₀ ≠ .east →
    ∀ L : ℕ, 12 ≤ L → ∀ P : DirectionWord L, SurvivingPrefix X d₀ P → ∀ φ : Phase, ∀ R : ℕ,
      trueContinuationSum X P φ R ≤ stationaryContinuationSum Q X d₀ φ
        (Q.project (lastWindowWord 10 P)) (wordVertex kernelStart P L) R

/-- `l:Bellman-soundness`: generic finitely branching nonnegative supersolutions bound
all stopped finite path sums and their full nonnegative sum. No normalization is assumed. -/
def BellmanSoundnessStatement : Prop :=
  ∀ α : Type, ∀ edges : α → List (α × ℝ), ∀ terminal : Set α,
    (∀ s, ∀ e ∈ edges s, 0 ≤ e.2) → (∀ s ∈ terminal, edges s = []) →
    ∀ g F : α → ℝ, (∀ s, 0 ≤ g s) → (∀ s, s ∉ terminal → g s = 0) →
    (∀ s, 0 ≤ F s) → (∀ s, g s + listBackward edges F s ≤ F s) →
    ∀ s, (∀ n : ℕ, (∑ j ∈ Finset.range (n + 1), ((listBackward edges)^[j]) g s) ≤ F s) ∧
      (∑' j : ℕ, ENNReal.ofReal (((listBackward edges)^[j]) g s)) ≤ ENNReal.ofReal (F s)

/-- `l:stationary-local-global`: all caps and finite integer rows imply a Bellman
supersolution on the entire lattice; outside values equal z and all inside values lie below z. -/
def StationaryLocalGlobalStatement : Prop :=
  (∀ t : ℚ, 0 ≤ t → t ≤ (coefficientCeiling t : ℚ) / certificateCoefficientScale) ∧
  ∀ Q : MemoryQuotient 10 3741, Q.Correct → ∀ X : PairType, ∀ d₀ : Compass, d₀ ≠ .east →
    ∀ C : StationaryData 3741, C.Passes Q X d₀ →
    (∀ φ a, freeApply Q (fun ψ b => (C.cap ψ b : ℚ) / certificateValueScale) φ a ≤
      (C.cap φ a : ℚ) / certificateValueScale) ∧
    ∀ φ a x, 0 ≤ C.potential φ a x ∧ C.potential φ a x ≤ (C.cap φ a : ℚ) / certificateValueScale ∧
      (x ∉ square (0, 0) certificateRadius → C.potential φ a x = (C.cap φ a : ℚ) / certificateValueScale) ∧
      stationaryReward X φ a x + stationaryApply Q X d₀ C.potential φ a x ≤ C.potential φ a x ∧
      ∀ R : ℕ, stationaryContinuationSum Q X d₀ φ a x R ≤ C.potential φ a x

/-- `l:prefix-domination`: each passing case bounds its complete true row at every cutoff,
using exact short ordering through twelve and surviving length-twelve prefixes. -/
def PrefixDominationStatement : Prop :=
  ∀ Q : MemoryQuotient 10 3741, Q.Correct → ∀ X : PairType, ∀ d₀ : Compass, d₀ ≠ .east →
    ∀ C : StationaryData 3741, C.Passes Q X d₀ → ∀ R : ℕ,
      firstDirectionPartialRow X d₀ R ≤ stationaryPrefixBound Q X d₀ C

/-- `l:kernel-reflection`: the only row reduction is B north/south reflection,
at every length and cutoff, with all prescribed ordering and h-reward retained. -/
def KernelReflectionStatement : Prop :=
  (∀ n : ℕ, ∀ w : DirectionWord n,
    let w' := fun i => reflectDirection (w i)
    (ClosedTrail .B w ↔ ClosedTrail .B w') ∧
    (FirstDirection w .north ↔ FirstDirection w' .south) ∧
    trailWeight kernelStart kernelIncoming w = trailWeight kernelStart kernelIncoming w' ∧
    kernelOrdering w = kernelOrdering w' ∧ closedContribution w = closedContribution w' ∧
    ∀ i : Fin n, wordStraight kernelIncoming w i = wordStraight kernelIncoming w' i ∧
      wordRevisit kernelStart w i = wordRevisit kernelStart w' i ∧
      (responsePairs w i).image (fun p => p.image (fun z => (z.1, -z.2))) = responsePairs w' i ∧
      ∀ p ∈ responsePairs w i,
        pairCoefficient w i p = pairCoefficient w' i (p.image (fun z => (z.1, -z.2))) ∧
        responsePairType p = responsePairType (p.image (fun z => (z.1, -z.2))) ∧
        pairShift .B p = pairShift .B (p.image (fun z => (z.1, -z.2)))) ∧
  ∀ R : ℕ, firstDirectionPartialRow .B .north R = firstDirectionPartialRow .B .south R

/-- `p:stationary-check`: actual finite arrays and a correct regenerated quotient,
with all five integer checks and exact denominator-cleared prefix ceilings. -/
def StationaryCheckStatement : Prop :=
  (square (0, 0) certificateRadius).card = 19881 ∧
  ∃ Q : MemoryQuotient 10 3741, Q.Correct ∧
    ∃ C : PairType × Compass → StationaryData 3741,
      ∀ k ∈ stationaryCases, (C k).Passes Q k.1 k.2 ∧
        (10^9 : ℚ) * stationaryPrefixBound Q k.1 k.2 (C k) ≤ stationaryPrefixCeiling k.1 k.2

/-- `l:stationary-assembly`: five exact case bounds, the B reflection and prefix
domination give both full nonnegative row bounds and all finite-cutoff H3 inequalities. -/
def StationaryAssemblyStatement : Prop :=
  ∀ Q : MemoryQuotient 10 3741, Q.Correct → ∀ C : PairType × Compass → StationaryData 3741,
    (∀ k ∈ stationaryCases, (C k).Passes Q k.1 k.2 ∧
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
