import AKLT.Defs.Kernel

noncomputable section
open scoped BigOperators

namespace AKLT.Defs

/-- `d:memory-automaton`: raw words use distinct unoriented bonds, with absolute labels. -/
def RawWindow {m : ℕ} (w : DirectionWord m) : Prop :=
  Function.Injective (wordBond (0, 0) w)

/-- The actual finite raw state set, not a stored list of purported states. -/
abbrev MemoryWindow (m : ℕ) := {w : DirectionWord m // RawWindow w}

noncomputable instance (m : ℕ) : Fintype (MemoryWindow m) := by
  classical
  exact Fintype.ofFinite _

/-- Last absolute direction, with an irrelevant totalization at memory zero. -/
def windowArrival {m : ℕ} (w : DirectionWord m) : Compass :=
  if h : 0 < m then w ⟨m - 1, by omega⟩ else .east

/-- `d:memory-automaton`: append and forget the oldest direction. -/
def windowSuccessor {m : ℕ} (w : DirectionWord m) (d : Compass) : DirectionWord m :=
  fun i => if h : i.val + 1 < m then w ⟨i.val + 1, h⟩ else d

/-- `d:memory-automaton`: initial reversal and every remembered used bond are excluded. -/
def WindowAdmissible {m : ℕ} (w : DirectionWord m) (d : Compass) : Prop :=
  d ≠ (windowArrival w).reverse ∧ ∀ i : Fin m,
    wordBond (0, 0) w i ≠
      {wordVertex (0, 0) w m, wordVertex (0, 0) w m + d.step}

/-- `d:memory-automaton`: the three detected departure kinds. -/
inductive StepKind where
  | straight | turn | revisit
  deriving DecidableEq, Repr

instance : Fintype StepKind :=
  ⟨{.straight, .turn, .revisit}, by intro k; cases k <;> simp⟩

/-- `d:memory-automaton`: revisit detection precedes straight/turn detection. -/
def windowKind {m : ℕ} (w : DirectionWord m) (d : Compass) : StepKind :=
  if 0 < departureCount (0, 0) w m (wordVertex (0, 0) w m) then .revisit
  else if d = windowArrival w then .straight else .turn

/-- `d:memorygrowth`: the exact one-step weights, with true revisit factor 1/5. -/
def kindWeight : StepKind → ℚ
  | .straight => passageFactor true / 3
  | .turn => passageFactor false / 3
  | .revisit => 1 / 5

/-- `d:memorygrowth`: the regenerated raw matrix, rather than trusted matrix data. -/
def memoryMatrix (m : ℕ) (ω ω' : MemoryWindow m) : ℚ := by
  classical
  exact ∑ d : Compass, if WindowAdmissible ω.val d ∧ windowSuccessor ω.val d = ω'.val
    then kindWeight (windowKind ω.val d) else 0

/-- `d:memorygrowth`: true length-n weight ending in a specified last window. -/
def lastWindowWord {n : ℕ} (m : ℕ) (w : DirectionWord n) : DirectionWord m :=
  fun i => if h : n - m + i.val < n then w ⟨n - m + i.val, h⟩ else .east

/-- True trail mass assigned to a raw memory window; used only when n is at least m. -/
def memoryTrailMass (m n : ℕ) (u : Plane) (incoming : Compass) (ω : MemoryWindow m) : ℚ := by
  classical
  exact ∑ w : DirectionWord n, if IsTrail u incoming w ∧ lastWindowWord m w = ω.val
    then trailWeight u incoming w else 0

/-- `l:automaton-quotient`: finite quotient data, with no correctness assumed in its fields. -/
structure MemoryQuotient (m q : ℕ) where
  project : DirectionWord m → Fin q
  representative : Fin q → DirectionWord m
  allowed : Fin q → Compass → Bool
  kind : Fin q → Compass → StepKind
  successor : Fin q → Compass → Fin q
  arrival : Fin q → Compass

/-- `l:automaton-quotient`: every required raw-to-quotient check, including nonrevisit arrivals. -/
def MemoryQuotient.Correct {m q : ℕ} (Q : MemoryQuotient m q) : Prop :=
  (∀ a, RawWindow (Q.representative a) ∧ Q.project (Q.representative a) = a) ∧
  ∀ w : DirectionWord m, RawWindow w → ∀ d : Compass,
    (Q.allowed (Q.project w) d = true ↔ WindowAdmissible w d) ∧
    (WindowAdmissible w d → Q.kind (Q.project w) d = windowKind w d ∧
      Q.successor (Q.project w) d = Q.project (windowSuccessor w d) ∧
      (windowKind w d ≠ .revisit → Q.arrival (Q.project w) = windowArrival w))

/-- `l:automaton-quotient`: the raw hypotheses on a surjective class map,
before choosing representatives and labelled quotient transitions. -/
def CompatibleProjection (m q : ℕ) (π : DirectionWord m → Fin q) : Prop :=
  (∀ a, ∃ w, RawWindow w ∧ π w = a) ∧
  ∀ w w' : DirectionWord m, RawWindow w → RawWindow w' → π w = π w' →
    (∀ d : Compass, (WindowAdmissible w d ↔ WindowAdmissible w' d) ∧
      windowKind w d = windowKind w' d ∧
      (WindowAdmissible w d → π (windowSuccessor w d) = π (windowSuccessor w' d))) ∧
    ((∃ d, WindowAdmissible w d ∧ windowKind w d ≠ .revisit) → windowArrival w = windowArrival w')

/-- `p:automaton10`: counts of labelled quotient edges, regenerated from admissibility/kind. -/
def quotientEdgeCount {m q : ℕ} (Q : MemoryQuotient m q) (k : StepKind) : ℕ :=
  (Finset.univ.filter fun e : Fin q × Compass => Q.allowed e.1 e.2 ∧ Q.kind e.1 e.2 = k).card

/-- `l:H2-dihedral`: the eight lattice symmetries as optional reflection followed by quarter turns. -/
abbrev SquareSymmetry := Fin 4 × Bool

/-- Direction action used to check the dihedral reduction without a supplied orbit list. -/
def turnLeft : Compass → Compass
  | .east => .north | .north => .west | .west => .south | .south => .east

def reflectDirection : Compass → Compass
  | .north => .south | .south => .north | d => d

def symmetryDirection (g : SquareSymmetry) (d : Compass) : Compass :=
  (turnLeft^[g.1.val]) (if g.2 then reflectDirection d else d)

/-- The induced componentwise action on raw words. -/
def symmetryWord {m : ℕ} (g : SquareSymmetry) (w : DirectionWord m) : DirectionWord m :=
  fun i => symmetryDirection g (w i)

/-- Same dihedral orbit, expressed by one of the eight actual symmetries. -/
def SameWindowOrbit {m : ℕ} (w w' : DirectionWord m) : Prop :=
  ∃ g : SquareSymmetry, symmetryWord g w = w'

end AKLT.Defs
