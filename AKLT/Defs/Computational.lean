import AKLT.Defs.Stationary

noncomputable section
open scoped BigOperators

namespace AKLT.Defs

/-- `l:alm`: exact true open-trail total with prescribed initial data. -/
def openTrailTotal (n : ℕ) (u : Plane) (incoming : Compass) : ℚ := by
  classical
  exact ∑ w : DirectionWord n, if IsTrail u incoming w then trailWeight u incoming w else 0

/-- `l:alm`: the max/min witness ratio over the actual raw state type. -/
def memoryWitnessRatio {m : ℕ} (v : MemoryWindow m → ℝ) : ℝ :=
  sSup (Set.range v) / sInf (Set.range v)

/-- `l:alm`: the displayed finite base constant, with one fixed start and incoming direction. -/
def memoryBaseConstant (m : ℕ) (q : ℝ) (v : MemoryWindow m → ℝ) : ℝ :=
  max (sSup {r : ℝ | ∃ j < m, r = (openTrailTotal j (0, 0) .east : ℝ) * q ^ (-(j : ℤ))})
    (memoryWitnessRatio v * (openTrailTotal m (0, 0) .east : ℝ) * q ^ (-(m : ℤ)))

/-- `l:automaton-quotient`: a general finite-phase raw backward operator. -/
def rawBackward (m p : ℕ)
    (weight : Fin p → Fin p → StepKind → Compass → Compass → Plane → ℚ)
    (terminal : Plane → Bool) (F : Fin p → DirectionWord m → Plane → ℚ)
    (φ : Fin p) (w : DirectionWord m) (x : Plane) : ℚ := by
  classical
  exact if terminal x then 0 else ∑ d : Compass, ∑ ψ : Fin p,
    if WindowAdmissible w d then weight φ ψ (windowKind w d) d (windowArrival w) x *
      F ψ (windowSuccessor w d) (x + d.step) else 0

/-- The matching quotient backward operator. Coefficients cannot inspect forgotten raw data. -/
def quotientBackward {m q : ℕ} (Q : MemoryQuotient m q) (p : ℕ)
    (weight : Fin p → Fin p → StepKind → Compass → Compass → Plane → ℚ)
    (terminal : Plane → Bool) (F : Fin p → Fin q → Plane → ℚ)
    (φ : Fin p) (a : Fin q) (x : Plane) : ℚ :=
  if terminal x then 0 else ∑ d : Compass, ∑ ψ : Fin p,
    if Q.allowed a d then weight φ ψ (Q.kind a d) d (Q.arrival a) x *
      F ψ (Q.successor a d) (x + d.step) else 0

/-- Finite sums of iterates, used for stopped continuation weights with no resolvent premise. -/
def finiteOperatorSum {α : Type*} (T : (α → ℚ) → (α → ℚ)) (g : α → ℚ) (R : ℕ) (s : α) : ℚ :=
  ∑ j ∈ Finset.range (R + 1), (T^[j]) g s

/-- Concatenation of finite compass words; all used-bond checks remain on the whole word. -/
def appendWords {n r : ℕ} (w : DirectionWord n) (v : DirectionWord r) : DirectionWord (n + r) :=
  fun i => if h : i.val < n then w ⟨i.val, h⟩ else v ⟨i.val - n, by omega⟩

/-- A prefix word, used only at L<=n; the default makes the indexing definition total. -/
def takeWord {n : ℕ} (w : DirectionWord n) (L : ℕ) : DirectionWord L :=
  fun i => if h : i.val < n then w ⟨i.val, h⟩ else .east

/-- The actual phase transition at one departure of a true word. -/
def truePhaseCoefficient {n : ℕ} (w : DirectionWord n) (i : Fin n) (φ ψ : Phase) : ℚ :=
  phaseTransition (if wordRevisit kernelStart w i then .revisit
    else if wordStraight kernelIncoming w i then .straight else .turn) (witnessKappa w i) φ ψ

/-- `l:phase-expansion`: the straight-first ordering used for every long closed trail. -/
def longOrdering {n : ℕ} (w : DirectionWord n) : List (Fin n) :=
  (firstVisitList w).filter (wordStraight kernelIncoming w) ++
    (firstVisitList w).filter (fun i => !wordStraight kernelIncoming w i)

/-- Exact phase contribution of a suffix, from one specified prefix phase. -/
def truePhaseSuffix {n : ℕ} (w : DirectionWord n) (L : ℕ) (φ : Phase) : ℚ :=
  let p := ((List.finRange n).drop L).foldl (fun p i ψ => ∑ χ : Phase, p χ *
    phaseTransition (if wordRevisit kernelStart w i then .revisit
      else if wordStraight kernelIncoming w i then .straight else .turn) (witnessKappa w i) χ ψ)
    (fun ψ => if ψ = φ then (1 : ℚ) else 0)
  ∑ ψ, p ψ * phaseTerminal ψ

/-- `l:stationary-domination`: the complete true suffix sum through a finite horizon. -/
def trueContinuationSum {L : ℕ} (X : PairType) (P : DirectionWord L) (φ : Phase) (R : ℕ) : ℚ := by
  classical
  exact ∑ r ∈ Finset.range (R + 1), ∑ v : DirectionWord r,
    if ClosedTrail X (appendWords P v) then truePhaseSuffix (appendWords P v) L φ else 0

/-- The stationary terminal reward is supported only on the target. -/
def stationaryReward (X : PairType) (φ : Phase) (_a : Fin 3741) (x : Plane) : ℚ :=
  if x = kernelTarget X then phaseTerminal φ else 0

/-- Finite stationary continuation sum on the actual lattice. -/
def stationaryContinuationSum (Q : MemoryQuotient 10 3741) (X : PairType) (d₀ : Compass)
    (φ : Phase) (a : Fin 3741) (x : Plane) (R : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (R + 1), ((stationaryApply Q X d₀)^[j]) (stationaryReward X) φ a x

/-- `l:Bellman-soundness`: a finitely branching operator specified by finite edge lists. -/
def listBackward {α : Type*} (edges : α → List (α × ℝ)) (F : α → ℝ) (s : α) : ℝ :=
  ((edges s).map fun e => e.2 * F e.1).sum

/-- Finite stopped continuation for the corrected zero-centre-edge operator. -/
def stationaryContinuationSumV2 (Q : MemoryQuotient 10 3741) (X : PairType) (d₀ : Compass)
    (φ : Phase) (a : Fin 3741) (x : Plane) (R : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (R + 1), ((stationaryApplyV2 Q X d₀)^[j]) (stationaryReward X) φ a x

end AKLT.Defs
