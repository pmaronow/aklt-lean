module
public import AKLT.Blueprint.Top.Computation
public import AKLT.Gen.Bellman.Main

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

/-! Shared, finite algebra for the H3 blueprint. No certificate arrays live here. -/
noncomputable section
open scoped BigOperators ENNReal
open AKLT.Defs

namespace AKLT.Blueprint.H3

/-- The true departure kind, with revisit taking precedence. -/
def trueKind {n : ℕ} (w : DirectionWord n) (i : Fin n) : StepKind :=
  if wordRevisit kernelStart w i then .revisit
  else if wordStraight kernelIncoming w i then .straight else .turn

/-- Forward multiplication of a phase row by one transition matrix. -/
def phaseUpdate (M : Phase → Phase → ℚ) (p : Phase → ℚ) : Phase → ℚ :=
  fun ψ => ∑ φ, p φ * M φ ψ

/-- Generic finite phase propagation, retaining the order of the supplied indices. -/
def phaseRun {ι : Type} (M : ι → Phase → Phase → ℚ)
    (indices : List ι) (p : Phase → ℚ) : Phase → ℚ :=
  indices.foldl (fun v i => phaseUpdate (M i) v) p

/-- A phase history with its unique change at index j. Only A→C and B→D are used. -/
def singleChange {n : ℕ} (k : Fin n → StepKind) (r : Fin n → ℚ)
    (j : Fin n) (φ ψ : Phase) : ℚ :=
  ∏ i : Fin n, if i.val < j.val then phaseDiagonal φ (k i)
    else if i = j then phaseTransition (k i) (r i) φ ψ else phaseDiagonal ψ (k i)

/-- Multipliers preceding a responding departure in the straight-first order. -/
def longMultiplier {n : ℕ} (w : DirectionWord n) (j : Fin n) : ℚ :=
  ∏ i : Fin n, if !wordRevisit kernelStart w i &&
    (if wordStraight kernelIncoming w j then
      wordStraight kernelIncoming w i && decide (i.val ≤ j.val)
    else wordStraight kernelIncoming w i || decide (i.val ≤ j.val))
    then passageFactor (wordStraight kernelIncoming w i) else 1

/-- Product through a selected index of a finite ordering. idxOf is used only for list members. -/
def orderedMultiplier {n : ℕ} (w : DirectionWord n) (l : List (Fin n)) (j : Fin n) : ℚ :=
  ((l.take (l.idxOf j + 1)).map (fun i => passageFactor (wordStraight kernelIncoming w i))).prod

/-- A single responding departure's reward in the long ordering. -/
def longRewardTerm {n : ℕ} (w : DirectionWord n) (j : Fin n) : ℚ :=
  if wordRevisit kernelStart w j then 0 else witnessKappa w j * longMultiplier w j

/-- Count arrivals, separately from the departure count in the shared definitions. -/
def arrivalCount {n : ℕ} (w : DirectionWord n) (z : Plane) : ℕ :=
  ((Finset.range n).filter fun j => wordVertex kernelStart w (j + 1) = z).card

/-- A finite set of genuinely dead neighbors; the center is included even when remote. -/
def trueDeadSet {n : ℕ} (w : DirectionWord n) (i : Fin n) : Finset Plane := by
  classical
  exact insert kernelCentre ((neighbours (wordVertex kernelStart w i.val)).filter (deadAt w i))

/-- Remembered raw word immediately before the indicated departure. -/
def suffixWindow {n : ℕ} (w : DirectionWord n) (j : ℕ) : DirectionWord 10 :=
  lastWindowWord 10 (takeWord w j)

/-- One lattice word's backward phase sum. Directions remain separate labels. -/
def stationaryWordValue (Q : MemoryQuotient 10 3741) (X : PairType) (d₀ : Compass) :
    List Compass → Phase → Fin 3741 → Plane → ℚ
  | [], φ, a, x => stationaryReward X φ a x
  | d :: ds, φ, a, x => ∑ ψ : Phase, stationaryCoefficient Q X d₀ φ a x d ψ *
      stationaryWordValue Q X d₀ ds ψ (Q.successor a d) (x + d.step)

/-- One length's entire h-weighted row, including length zero. -/
def kernelLengthRow (X : PairType) (n : ℕ) : ℚ := by
  classical
  exact ∑ w : DirectionWord n, if ClosedTrail X w then closedContribution w else 0

/-- All shifts that can occur at this length, defined without a geometric estimate. -/
def lengthShifts (X : PairType) (n : ℕ) : Finset ℕ := by
  classical
  exact Finset.univ.biUnion fun w : DirectionWord n =>
    Finset.univ.biUnion fun i : Fin n => (responsePairs w i).image (pairShift X)

/-- Reflection in the horizontal axis, fixing the sites for row B. -/
def reflectSite (x : Plane) : Plane := (x.1, -x.2)

def reflectWord {n : ℕ} (w : DirectionWord n) : DirectionWord n :=
  fun i => reflectDirection (w i)

@[simp] theorem reflectSite_involutive (x : Plane) : reflectSite (reflectSite x) = x := by
  cases x
  simp [reflectSite]

@[simp] theorem reflectDirection_involutive (d : Compass) :
    reflectDirection (reflectDirection d) = d := by cases d <;> rfl

@[simp] theorem reflectWord_involutive {n : ℕ} (w : DirectionWord n) :
    reflectWord (reflectWord w) = w := by
  funext i
  exact reflectDirection_involutive (w i)

/-- The reflection bijection preserves multiplicities in finite word sums. -/
def reflectWordEquiv (n : ℕ) : DirectionWord n ≃ DirectionWord n :=
  ⟨reflectWord, reflectWord, reflectWord_involutive, reflectWord_involutive⟩

/-- Taking the specified prefix of a concatenation retains every letter exactly. -/
theorem takeWord_append {L r : ℕ} (P : DirectionWord L) (v : DirectionWord r) :
    takeWord (appendWords P v) L = P := by
  funext i
  simp [takeWord, appendWords, show i.val < L + r by omega]

end AKLT.Blueprint.H3
