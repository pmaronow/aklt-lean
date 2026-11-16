import AKLT.Blueprint.Top.ComputationV2
import CertData.H3.Kernel.Production.Batching
import CertData.H3.Kernel.Automaton
import CertData.H3.Kernel.Prefix
set_option maxRecDepth 100000

/-! Closed production proof interfaces. All mathematical leaf obligations are
definitions of Props. The only proved declaration is a blueprint assembly. -/
namespace CertData.H3.Bridge
open AKLT.Cert.H3 AKLT.Cert.H3.Production AKLT.Defs AKLT.Gen.Packed

def WalkRepresents {n : Nat} (u : Plane) (incoming : Nat) (w : DirectionWord n) (s : Walk) : Prop :=
  s.depth=n ∧ s.pos=wordVertex u w n ∧
  s.incoming=(if n=0 then incoming else directionCode (windowArrival w)) ∧
  s.code=encodeWord w % 1048576 ∧
  s.departed=((List.finRange n).reverse.map fun i => wordVertex u w i.val) ∧
  s.used=((List.finRange n).reverse.map fun i => bond (wordVertex u w i.val) (wordVertex u w (i.val+1)))

def CodeDecodeLeaf : Prop := ∀ (n c : Nat), c<4^n → encodeWord (decodeWord n c)=c
def CodeEncodeLeaf : Prop := ∀ (n : Nat) (w : DirectionWord n),
  encodeWord w<4^n ∧ decodeWord n (encodeWord w)=w
def LastWindowCodeLeaf : Prop := ∀ (n : Nat), 10 ≤ n → ∀ w : DirectionWord n,
  encodeWord (lastWindowWord 10 w)=encodeWord w % 1048576
def SuccessorCodeLeaf : Prop := ∀ (c : Nat), c<1048576 → ∀ d : Fin 4,
  encodeWord (windowSuccessor (decodeWord 10 c) (direction d.val))=(c*4+d.val)%1048576
def RawReplaySoundLeaf : Prop := ∀ (n c : Nat), n ≤ 10 → c<4^n → ∀ s : Walk,
  replayRaw n c rawInitial=some s → RawWindow (decodeWord n c) ∧
    WalkRepresents (0,0) 0 (decodeWord n c) s
def RawReplayCompleteLeaf : Prop := ∀ (n c : Nat), n ≤ 10 → c<4^n →
  RawWindow (decodeWord n c) → (replayRaw n c rawInitial).isSome=true
def LegalDirectionLeaf : Prop := ∀ (w : DirectionWord 10) (s : Walk),
  RawWindow w → WalkRepresents (0,0) 0 w s → ∀ d : Fin 4,
    ((d.val != rev s.incoming) && s.legal d.val)=true ↔ WindowAdmissible w (direction d.val)
def RevisitLeaf : Prop := ∀ (n : Nat) (u : Plane) (incoming : Nat) (w : DirectionWord n) (s : Walk),
  WalkRepresents u incoming w s →
    (s.departed.contains s.pos=true ↔ 0<departureCount u w n (wordVertex u w n))
def RawRowSoundLeaf : Prop := ∀ (G : Graph) (c : Nat), c<1048576 → ∀ s : Walk,
  RawWindow (decodeWord 10 c) → WalkRepresents (0,0) 0 (decodeWord 10 c) s →
    rawRow G s=true → CorrectAt G.quotient (decodeWord 10 c)

def SpanRepresents (G : Graph) : Prop := ∀ start count : Nat,
  count ≤ 256 → start%4096+count ≤ 4096 → start+count ≤ 1048576 →
  Fits (G.classSpan start count) 12 count ∧
    ∀ i<count, lane (G.classSpan start count) 12 i=G.classAt (start+i)
def RawTrieCoverageLeaf : Prop := ∀ G : Graph, SpanRepresents G → (rawBatch G 0 4096).ok=true →
  ∀ c : Fin (4^10), G.classAt c.val<3741 ↔ RawWindow (decodeWord 10 c.val)
def RawTrieProjectionLeaf : Prop := ∀ G : Graph, SpanRepresents G →
  (rawBatch G 0 4096).ok=true → representativeBatch G 0 3741=true → G.quotient.Correct
def RawTrieBoundsLeaf : Prop := ∀ G : Graph, SpanRepresents G →
  (rawBatch G 0 4096).ok=true → ∀ c : Fin (4^10), G.classAt c.val ≤ 3741
def RepresentativeBoundsLeaf : Prop := ∀ G : Graph, representativeBatch G 0 3741=true →
  ∀ a : Fin 3741, G.representative a.val<4^10
def FieldCheckSoundLeaf : Prop := ∀ G : Graph, fieldBatch G 0 3741=true →
  ∀ (a : Fin 3741) (d : Compass), G.dest a.val (directionCode d) ≤ 3741 ∧
    (G.dest a.val (directionCode d)=0 ↔ G.kind a.val (directionCode d)=3) ∧
    (G.dest a.val (directionCode d) ≠ 0 → G.kind a.val (directionCode d)<3)
def RawTrieCountLeaf : Prop := ∀ G : Graph,
  (rawBatch G 0 4096).count=Fintype.card (MemoryWindow 10)
def EdgeCountLeaf : Prop := ∀ G : Graph, edgeCounts G=(2516,5032,1872) →
  quotientEdgeCount G.quotient .straight=2516 ∧ quotientEdgeCount G.quotient .turn=5032 ∧
    quotientEdgeCount G.quotient .revisit=1872
def IntervalCoverageLeaf : Prop := ∀ parts : List (Nat × Nat), ∀ limit : Nat,
  intervalCheck parts limit=true → ∀ i<limit,
    ∃! j : Fin parts.length, ((parts[j.val]?.getD (0,0)).1  ≤  i) ∧
      (i < (parts[j.val]?.getD (0,0)).1 + (parts[j.val]?.getD (0,0)).2)

def EndpointBinding (data lookup : Tables) : Prop := ∀ (p : Fin 4) (a : Fin 3741) (x : Point),
  endpointInside x=true → endpointValue lookup p.val a.val x=data.data.extended (phase p.val) a x
def RectangleLeaf : Prop := ∀ P : Nat, Fits P 80 19881 → ∀ x : Point, endpointInside x=true →
  lane (rectangle P) 80 (endpointIndex x)=lane P 80 (siteIndex x)
def EndpointBoxLeaf : Prop := ∀ w : DirectionWord 12, endpointInside (wordVertex kernelStart w 12)=true
def PullLeaf : Prop := ∀ (P Z : Nat) (d : Compass), Fits P 80 19881 → Z<2^26 → ∀ s<19881,
  lane (pull P Z d) 80 s=if inBox (gridSite s+d.step) then lane P 80 (siteIndex (gridSite s+d.step)) else Z

/-- One phase/window's exact V2 finite clauses. -/
def PlaneSpec (G : Graph) (T : Tables) (X : PairType) (d₀ : Compass) (φ : Phase) (a : Fin 3741) : Prop :=
  0<T.capFn φ a ∧ ((φ=.C ∨ φ=.D) → certificateValueScale ≤ T.capFn φ a) ∧
  ((∑ d : Compass, ∑ ψ : Phase, coefficientCeiling (freeCoefficient G.quotient φ a d ψ)*
    T.capFn ψ (G.quotient.successor a d)) ≤ certificateCoefficientScale*T.capFn φ a) ∧
  (∀ x : square (0,0) certificateRadius, T.data.value φ a x ≤ T.capFn φ a) ∧
  (T.data.extended φ a kernelCentre=0 ∧
    (T.data.extended φ a (kernelTarget X) : ℚ)=certificateValueScale*phaseTerminal φ) ∧
  ∀ x : square (0,0) certificateRadius, x.val ≠ kernelCentre → x.val ≠ kernelTarget X →
    (∑ d : Compass, ∑ ψ : Phase, coefficientCeiling (stationaryCoefficientV2 G.quotient X d₀ φ a x.val d ψ)*
      T.data.extended ψ (G.quotient.successor a d) (x.val+d.step)) ≤ certificateCoefficientScale*T.data.value φ a x

def OrdinaryMaskLeaf : Prop := ∀ (X : PairType) (d₀ : Compass), (X,d₀)∈stationaryCases →
  ∀ s<19881, lane (ordinaryMask X d₀) 80 s =
    if gridSite s=kernelCentre ∨ gridSite s=kernelTarget X ∨ gridSite s=kernelStart ∨
      gridSite s=kernelStart+d₀.step then 0 else 2^80-1
def KnownMaskLeaf : Prop := ∀ (d₀ d : Compass), d₀ ≠ .east → ∀ s<19881,
  lane (knownMask d₀ d) 80 s =
    if (gridSite s=kernelStart ∧ d ≠ d₀) ∨
      (gridSite s=kernelStart+d₀.step ∧ d ≠ d₀.reverse) then 2^80-1 else 0
def DeadMaskLeaf : Prop := ∀ j : Fin 5, ∀ s<19881, lane (deadMask j.val) 80 s =
  if (if j.val<4 then gridSite s = -(direction j.val).step
      else ∀ d : Compass, gridSite s ≠ -d.step) then 2^80-1 else 0

def CentreZeroV2Leaf : Prop := ∀ (Q : MemoryQuotient 10 3741) (C : StationaryData 3741)
    (X : PairType) (d₀ : Compass), (∀ φ a, C.extended φ a kernelCentre=0) → ∀ φ a x,
  (∑ d : Compass, ∑ ψ : Phase, coefficientCeiling (stationaryCoefficient Q X d₀ φ a x d ψ)*
    C.extended ψ (Q.successor a d) (x+d.step)) =
  ∑ d : Compass, ∑ ψ : Phase, coefficientCeiling (stationaryCoefficientV2 Q X d₀ φ a x d ψ)*
    C.extended ψ (Q.successor a d) (x+d.step)
def TableBounds (T : Tables) : Prop := ∀ (φ : Phase) (a : Fin 3741),
  0<T.capFn φ a ∧ T.capFn φ a<2^26 ∧ Fits (T.planeFn φ a) 80 19881 ∧
    lane (T.planeFn φ a) 80 (siteIndex kernelCentre)=0
def TableBoundsLeaf : Prop := ∀ (G : Graph) (T : Tables) (X : PairType) (d₀ : Compass),
  (∀ (φ : Phase) (a : Fin 3741), planeCheck G T X d₀ (phaseKey (phaseCode φ) a.val)=true) → TableBounds T
def RowTermsV2Leaf : Prop := ∀ (G : Graph) (T : Tables) (X : PairType) (d₀ : Compass),
  G.quotient.Correct → TableBounds T → (X,d₀)∈stationaryCases → ∀ (φ : Phase) (a : Fin 3741),
  ∀ s<19881, gridSite s ≠ kernelCentre → gridSite s ≠ kernelTarget X →
  component 80 s (rowTerms G.quotient T.planeFn T.capFn X d₀ φ a)=
    ∑ d : Compass, ∑ ψ : Phase,
      coefficientCeiling (stationaryCoefficientV2 G.quotient X d₀ φ a (gridSite s) d ψ)*
        T.data.extended ψ (G.quotient.successor a d) (gridSite s+d.step)

def FreeRowLeaf : Prop := ∀ (G : Graph) (T : Tables), G.quotient.Correct → ∀ (φ : Phase) (a : Fin 3741),
  freeRow G T (phaseCode φ) a.val =
    ∑ d : Compass, ∑ ψ : Phase, coefficientCeiling (freeCoefficient G.quotient φ a d ψ)*T.capFn ψ (G.quotient.successor a d)
def PlaneSoundLeaf : Prop := ∀ (G : Graph) (T : Tables) (X : PairType) (d₀ : Compass),
  G.quotient.Correct → TableBounds T → (X,d₀)∈stationaryCases → ∀ (φ : Phase) (a : Fin 3741),
  planeCheck G T X d₀ (phaseKey (phaseCode φ) a.val)=true → PlaneSpec G T X d₀ φ a

def deadSet (mask : Nat) : Finset Plane :=
  (Finset.univ.filter fun d : Compass => mask.testBit (directionCode d)).image Compass.step
def ExactValid (E : Exact) : Prop := 0<E.denominator ∧
  (E.straight : ℚ)/E.denominator=passageFactor true/3 ∧
  (E.turn : ℚ)/E.denominator=passageFactor false/3 ∧
  (E.third : ℚ)/E.denominator=1/3 ∧ (E.fifth : ℚ)/E.denominator=1/5 ∧
  ∀ a d : Fin 4, direction d.val ≠ (direction a.val).reverse → ∀ mask : Fin 16,
    (E.reward a.val d.val mask.val : ℚ)/E.denominator =
      relaxedReward (0,0) (direction a.val) (direction d.val) (deadSet mask.val) ∧
    (E.response a.val d.val mask.val : ℚ)/E.denominator =
      passageFactor (decide (a.val=d.val))*relaxedReward (0,0) (direction a.val) (direction d.val) (deadSet mask.val)/3

def phaseNumerator (s : PrefixState) : Phase → Nat
  | .A => s.A | .B => s.B | .C => s.C | .D => s.D
def PrefixRepresents (E : Exact) {n : Nat} (w : DirectionWord n) (s : PrefixState) : Prop :=
  WalkRepresents kernelStart 2 w s.walk ∧
  (∀ φ : Phase, prefixPhases w φ=(phaseNumerator s φ : ℚ)/(E.denominator^n : Nat)) ∧
  trailBaseWeight kernelStart w=(s.base : ℚ)/(E.denominator^n : Nat) ∧
  s.items.map RewardItem.time=(firstVisitList w).reverse.map Fin.val ∧
  ∀ item∈s.items, ∃ i : Fin n, i.val=item.time ∧ item.straight=wordStraight kernelIncoming w i ∧
    (item.reward : ℚ)/E.denominator=witnessKappa w i
def PrefixReplaySoundLeaf : Prop := ∀ (E : Exact), ExactValid E → ∀ (X : PairType)
  (d₀ : Fin 4) (n c : Nat), 1 ≤ n → n ≤ 12 → c<4^n → ∀ s : PrefixState,
  replayPrefix E X d₀.val n c initial=some s →
    PrefixRepresents E (decodeWord n c) s ∧ SurvivingPrefix X (direction d₀.val) (decodeWord n c)
def PrefixReplayCompleteLeaf : Prop := ∀ (E : Exact), ExactValid E → ∀ (X : PairType)
  (d₀ : Fin 4) (n c : Nat), 1 ≤ n → n ≤ 12 → c<4^n →
  SurvivingPrefix X (direction d₀.val) (decodeWord n c) →
    (replayPrefix E X d₀.val n c initial).isSome=true
def PrefixStepLeaf : Prop := ∀ (E : Exact), ExactValid E → ∀ (n : Nat) (w : DirectionWord n)
  (s : PrefixState), PrefixRepresents E w s → ∀ d : Fin 4,
  IsTrail kernelStart kernelIncoming (appendWords w (fun _ : Fin 1 => direction d.val)) →
    PrefixRepresents E (appendWords w (fun _ : Fin 1 => direction d.val)) (transition E s d.val)
def ShortComparatorLeaf : Prop := ∀ E : Exact, ExactValid E → ∀ (n : Nat) (w : DirectionWord n)
  (s : PrefixState), PrefixRepresents E w s → ∀ (a b : RewardItem), a∈s.items → b∈s.items →
    ∀ i j : Fin n, i.val=a.time → j.val=b.time → itemLE E a b=shortOrderLE w i j
def ShortValueLeaf : Prop := ∀ E : Exact, ExactValid E → ∀ (n : Nat), n ≤ 12 →
  ∀ (w : DirectionWord n) (s : PrefixState), PrefixRepresents E w s →
    (shortValue E s : ℚ)/(E.denominator^36 : Nat)=closedContribution w

noncomputable def semanticStem (G : Graph) (T : Tables) (X : PairType) (d₀ : Compass) (depth code : Nat) : ℚ :=
  prefixShard G.quotient T.data X d₀ (fun e : Fin (4^(12-depth)) => decodeWord 12 (code*4^(12-depth)+e.val)) +
  ∑ n∈Finset.Icc (depth+1) 12, ∑ e : Fin (4^(n-depth)),
    let w := decodeWord n (code*4^(n-depth)+e.val)
    if ClosedTrail X w ∧ FirstDirection w d₀ then closedContribution w else 0
noncomputable def semanticBatch (G : Graph) (T : Tables) (X : PairType) (d₀ : Compass)
    (depth start count : Nat) : ℚ := ((List.range count).map fun i => semanticStem G T X d₀ depth (start+i)).sum
def resultValue (E : Exact) (r : PrefixResult) : ℚ :=
  (r.short : ℚ)/(E.denominator^36 : Nat)+(r.tail : ℚ)/(E.denominator^12*65536 : Nat)
def PrefixBatchSoundLeaf : Prop := ∀ (G : Graph) (T lookup : Tables) (E : Exact),
  ExactValid E → G.quotient.Correct → EndpointBinding T lookup → ∀ (X : PairType) (d₀ : Fin 4)
  (depth start count : Nat), 1 ≤ depth → depth ≤ 12 → start+count ≤ 4^depth →
    (prefixBatch G lookup E X d₀.val depth start count).ok=true →
    resultValue E (prefixBatch G lookup E X d₀.val depth start count)=
      semanticBatch G T X (direction d₀.val) depth start count
def EarlySoundLeaf : Prop := ∀ (E : Exact), ExactValid E → ∀ (X : PairType) (d₀ : Fin 4) depth,
  depth ≤ 12 → resultValue E (earlyDFS E X d₀.val depth initial)=firstDirectionPartialRow X (direction d₀.val) depth
def PrefixPartitionLeaf : Prop := ∀ (G : Graph) (T : Tables) (X : PairType) (d₀ : Compass) depth,
  1 ≤ depth → depth ≤ 12 → stationaryPrefixBound G.quotient X d₀ T.data =
    firstDirectionPartialRow X d₀ depth + semanticBatch G T X d₀ depth 0 (4^depth)
def NumericScaleLeaf : Prop := ∀ (E : Exact), 0<E.denominator → ∀ r : PrefixResult,
  resultValue E r=(finalNumerator E r : ℚ)/finalDenominator E
def RationalCeilingLeaf : Prop := ∀ (E : Exact), 0<E.denominator → ∀ (r : PrefixResult) c,
  ceilingCheck E r c=true → (10^9 : ℚ)*resultValue E r ≤ c

def PlaneBatchSoundLeaf : Prop := ∀ (G : Graph) (T : Tables) (X : PairType) (d₀ : Compass)
    (start count : Nat), planeBatch G T X d₀ start count=true →
  ∀ i<count, planeCheck G T X d₀ (start+i)=true
def RowCoverageLeaf : Prop := ∀ (G : Graph) (T : Tables) (X : PairType) (d₀ : Compass)
    (parts : List (Nat × Nat)), intervalCheck parts 14964=true →
  (∀ part∈parts, planeBatch G T X d₀ part.1 part.2=true) →
  ∀ (φ : Phase) (a : Fin 3741), planeCheck G T X d₀ (phaseKey (phaseCode φ) a.val)=true
def EndpointTableSoundLeaf : Prop := ∀ (G : Graph) (T lookup : Tables) (X : PairType) (d₀ : Compass),
  (∀ (φ : Phase) (a : Fin 3741), planeCheck G T X d₀ (phaseKey (phaseCode φ) a.val)=true) →
  (∀ key<14964, T.endpoint key=lookup.endpoint key) → EndpointBinding T lookup
def ResultAddLeaf : Prop := ∀ (E : Exact) (r s : PrefixResult),
  resultValue E (r.add s)=resultValue E r+resultValue E s

def replayedResult (G : Graph) (lookup : Tables) (E : Exact) (X : PairType) (d₀ depth : Nat)
    (parts : List (Nat × Nat)) : PrefixResult :=
  (earlyDFS E X d₀ depth initial :: parts.map (fun part =>
    prefixBatch G lookup E X d₀ depth part.1 part.2)).foldl PrefixResult.add zeroResult

def SemanticBatchSplitLeaf : Prop := ∀ (G : Graph) (T : Tables) (X : PairType) (d₀ : Compass)
    (depth : Nat) (parts : List (Nat × Nat)), intervalCheck parts (4^depth)=true →
  semanticBatch G T X d₀ depth 0 (4^depth)=
    (parts.map fun part => semanticBatch G T X d₀ depth part.1 part.2).sum

def PrefixResultsJoinLeaf : Prop := PrefixBatchSoundLeaf → EarlySoundLeaf → PrefixPartitionLeaf →
  ∀ (G : Graph) (T lookup : Tables) (E : Exact) (X : PairType) (d₀ : Fin 4)
    (depth : Nat) (parts : List (Nat × Nat)),
  ExactValid E → G.quotient.Correct → EndpointBinding T lookup → 1 ≤ depth → depth ≤ 12 →
  intervalCheck parts (4^depth)=true → (replayedResult G lookup E X d₀.val depth parts).ok=true →
  stationaryPrefixBound G.quotient X (direction d₀.val) T.data=
    resultValue E (replayedResult G lookup E X d₀.val depth parts)

def UniformRowCoverageLeaf : Prop := ∀ (G : Graph) (T : Tables) (X : PairType) (d₀ : Compass)
    (group : Nat), 0<group →
  (∀ i : Fin ((14964+group-1)/group),
    planeBatch G T X d₀ (i.val*group) (min group (14964-i.val*group))=true) →
  ∀ (φ : Phase) (a : Fin 3741), planeCheck G T X d₀ (phaseKey (phaseCode φ) a.val)=true

/-- One generic join replaces five copies mentioning unbuilt literal datasets. -/
def PrefixFamilyJoinLeaf : Prop := PrefixBatchSoundLeaf → EarlySoundLeaf → PrefixPartitionLeaf →
  ∀ (G : Graph) (T lookup : Tables) (E : Exact) (X : PairType) (d₀ : Fin 4)
    (depth group : Nat) (early : PrefixResult) (expected : Nat → PrefixResult),
  ExactValid E → G.quotient.Correct → EndpointBinding T lookup →
  1 ≤ depth → depth ≤ 12 → 0<group →
  earlyDFS E X d₀.val depth initial=early →
  (∀ i : Fin ((4^depth+group-1)/group),
    prefixBatch G lookup E X d₀.val depth (i.val*group) (min group (4^depth-i.val*group))=expected i.val) →
  (∀ i : Fin ((4^depth+group-1)/group), (expected i.val).ok=true) →
  stationaryPrefixBound G.quotient X (direction d₀.val) T.data=
    resultValue E ((early :: (List.finRange ((4^depth+group-1)/group)).map
      (fun i => expected i.val)).foldl PrefixResult.add zeroResult)

def SharedCaseLeaves : Prop := TableBoundsLeaf ∧ PlaneSoundLeaf ∧ PrefixBatchSoundLeaf ∧
  EarlySoundLeaf ∧ PrefixPartitionLeaf ∧ RationalCeilingLeaf

def ProductionCaseLeaves : Prop := SharedCaseLeaves ∧ UniformRowCoverageLeaf ∧
  EndpointTableSoundLeaf ∧ PrefixFamilyJoinLeaf

def CaseV2 (X : PairType) (d₀ : Compass) : Prop := ∃ C : StationaryData 3741,
  C.PassesV2 Automaton10Data.supplied X d₀ ∧
    (10^9 : ℚ)*stationaryPrefixBound Automaton10Data.supplied X d₀ C ≤ stationaryPrefixCeiling X d₀

/-- Blueprint assembly: collect the exact phase/window clauses, without proving a semantic leaf. -/
theorem passesV2_of_plane_specs (G : Graph) (T : Tables) (X : PairType) (d₀ : Compass)
    (h : ∀ φ a, PlaneSpec G T X d₀ φ a) : T.data.PassesV2 G.quotient X d₀ :=
  ⟨(fun φ a => (h φ a).1),
   (fun a => ⟨(h .C a).2.1 (Or.inl rfl),(h .D a).2.1 (Or.inr rfl)⟩),
   (fun φ a => (h φ a).2.2.1), (fun φ a => (h φ a).2.2.2.1),
   (fun φ a => (h φ a).2.2.2.2.1), (fun φ a => (h φ a).2.2.2.2.2)⟩

/-- Assembly from the closed row/ceiling leaves and explicit computational evidence. -/
theorem caseV2_of_checks (G : Graph) (T : Tables) (E : Exact) (X : PairType) (d₀ : Compass)
    (r : PrefixResult) (c : Nat) (hQ : G.quotient=Automaton10Data.supplied)
    (hcorrect : G.quotient.Correct) (hcase : (X,d₀)∈stationaryCases)
    (hrows : ∀ (φ : Phase) (a : Fin 3741), planeCheck G T X d₀ (phaseKey (phaseCode φ) a.val)=true)
    (hJ : stationaryPrefixBound G.quotient X d₀ T.data=resultValue E r)
    (hvalid : ExactValid E) (hcheck : ceilingCheck E r c=true)
    (hc : (c : ℚ)=stationaryPrefixCeiling X d₀)
    (h : SharedCaseLeaves) : CaseV2 X d₀ := by
  rcases h with ⟨hb,hsound,_,_,_,hceiling⟩
  have hbounds := hb G T X d₀ hrows
  have hpasses := passesV2_of_plane_specs G T X d₀
    (fun φ a => hsound G T X d₀ hcorrect hbounds hcase φ a (hrows φ a))
  have hbound := hceiling E hvalid.1 r c hcheck
  rw [←hJ,hc] at hbound
  exact ⟨T.data,
    Eq.mp (congrArg (fun Q : MemoryQuotient 10 3741 => T.data.PassesV2 Q X d₀) hQ) hpasses,
    Eq.mp (congrArg (fun Q : MemoryQuotient 10 3741 =>
      (10^9 : ℚ)*stationaryPrefixBound Q X d₀ T.data ≤ stationaryPrefixCeiling X d₀) hQ) hbound⟩

/-- Finite case assembly, independent of the generated data representation. -/
theorem stationaryV2_of_cases (hsquare : (square (0,0) certificateRadius).card=19881)
    (hq : Automaton10Data.supplied.Correct)
    (hbn : CaseV2 .B .north) (hbw : CaseV2 .B .west) (hcn : CaseV2 .C .north)
    (hcw : CaseV2 .C .west) (hcs : CaseV2 .C .south) : AKLT.Blueprint.Top.StationaryCheckStatementV2 := by
  rcases hbn with ⟨CBN,hbn⟩
  rcases hbw with ⟨CBW,hbw⟩
  rcases hcn with ⟨CCN,hcn⟩
  rcases hcw with ⟨CCW,hcw⟩
  rcases hcs with ⟨CCS,hcs⟩
  let C : PairType × Compass → StationaryData 3741 := fun
    | (.B,.north) => CBN | (.B,.west) => CBW | (.C,.north) => CCN
    | (.C,.west) => CCW | (.C,.south) => CCS | _ => CBN
  refine ⟨hsquare,hq,C,?_⟩
  rintro ⟨X,d⟩ hk
  cases X <;> cases d
  · simp [stationaryCases] at hk
  · exact hbn
  · exact hbw
  · simp [stationaryCases] at hk
  · simp [stationaryCases] at hk
  · exact hcn
  · exact hcw
  · exact hcs

#print axioms caseV2_of_checks
#print axioms stationaryV2_of_cases
#print axioms passesV2_of_plane_specs
end CertData.H3.Bridge
