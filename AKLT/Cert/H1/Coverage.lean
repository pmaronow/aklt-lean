module
public import AKLT.Defs.OperatorContracts

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

namespace AKLT.Cert.H1
open AKLT.Defs

def ringSites : List Plane :=
  [(1,0), (1,1), (0,1), (-1,1), (-1,0), (-1,-1), (0,-1), (1,-1)]

/-- Fixed undirected template edges: four center, eight ring, and four tip edges. -/
def templateEdges : List (Plane × Plane) :=
  [((0,0),(1,0)), ((0,0),(0,1)), ((0,0),(-1,0)), ((0,0),(0,-1)),
   ((1,0),(1,1)), ((1,1),(0,1)), ((0,1),(-1,1)), ((-1,1),(-1,0)),
   ((-1,0),(-1,-1)), ((-1,-1),(0,-1)), ((0,-1),(1,-1)), ((1,-1),(1,0)),
   ((1,0),(2,0)), ((0,1),(0,2)), ((-1,0),(-2,0)), ((0,-1),(0,-2))]

def presentBond (π : PatternData) (a b : Plane) : Bool :=
  decide ((a,b) ∈ π.bonds ∨ (b,a) ∈ π.bonds)

def reflectPoint (reflect : Bool) (x : Plane) : Plane :=
  if reflect then (-x.1,x.2) else x

/-- Fixed-width positional encoding, least significant site/edge first. -/
def encodeDigits (base : Nat) : List Nat → Nat
  | [] => 0
  | a :: as => a + base * encodeDigits base as

def statusDigit : Status → Nat
  | .X => 0
  | .U => 1
  | .D => 2

/-- The effective code is derived from Defs, including deletion of isolated sites.
The unused kept sets at removed sites and covering tips do not enter the key. -/
def reflectedPatternCode (π : PatternData) (reflect : Bool) : Nat :=
  let status := encodeDigits 3 (ringSites.map fun x =>
    let y := reflectPoint reflect x
    if patternDegree π y == 0 then 0 else statusDigit (π.statusAt y))
  let edges := encodeDigits 2 (templateEdges.map fun (a,b) =>
    (presentBond π (reflectPoint reflect a) (reflectPoint reflect b)).toNat)
  let out := if π.outgoing == .north then 1
    else if (π.outgoing == .east) != reflect then 0 else 2
  (status * 65536 + edges)*3 + out

def effectivePatternCode (π : PatternData) : Nat :=
  min (reflectedPatternCode π false) (reflectedPatternCode π true)

def thresholdNumerator (code : Nat) : Nat := if code % 3 == 1 then 961 else 187
def thresholdDenominator (code : Nat) : Nat := if code % 3 == 1 then 1000 else 200

def strictlyIncreasing : List Nat → Bool
  | [] => true
  | [_] => true
  | a :: b :: xs => decide (a < b) && strictlyIncreasing (b :: xs)

theorem strictlyIncreasing_sound (xs : List Nat) :
    strictlyIncreasing xs = true → xs.Pairwise (· < ·) := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    cases xs with
    | nil => simp
    | cons b bs =>
      intro h
      simp only [strictlyIncreasing, Bool.and_eq_true, decide_eq_true_eq] at h
      exact List.pairwise_cons_cons_iff_of_trans.mpr ⟨h.1, ih h.2⟩

#print axioms strictlyIncreasing_sound

/-- Closed coverage obligation; the catalog is data, not a hypothesis in a theorem. -/
def CoverageStatement (codes : List Nat) : Prop :=
  codes.length = 7962 ∧ codes.Nodup ∧
    ∀ π : PatternData, π.Covered → effectivePatternCode π ∈ codes

/-- The normalization/reflection step must transfer the inequality on all twenty
original slots. Code equality alone is not asserted to prove this obligation. -/
def EffectiveTransferStatement : Prop :=
  ∀ π ρ : PatternData, π.Covered → ρ.Covered →
    effectivePatternCode π = effectivePatternCode ρ →
    (∀ m : Fin 20 → UnitVector,
      0 ≤ patternCurrent ρ m -
        ((thresholdNumerator (effectivePatternCode ρ) : ℝ) /
          thresholdDenominator (effectivePatternCode ρ)) * patternNext ρ m) →
    ∀ m : Fin 20 → UnitVector,
      0 ≤ patternCurrent π m -
        ((thresholdNumerator (effectivePatternCode π) : ℝ) /
          thresholdDenominator (effectivePatternCode π)) * patternNext π m

end AKLT.Cert.H1
