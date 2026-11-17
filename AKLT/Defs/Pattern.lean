module
public import AKLT.Defs.Trails

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators

namespace AKLT.Defs

/-- `d:pattern`: the thirteen sites in the radius-two taxicab template. -/
def templateSites : Finset Plane := (square (0, 0) 2).filter fun z => latticeDist z (0, 0) ≤ 2

/-- `d:pattern`: the four covering tips. -/
def templateTips : Finset Plane := {(2, 0), (0, 2), (-2, 0), (0, -2)}

/-- `d:pattern`: the four corners, each with both external slots. -/
def templateCorners : Finset Plane := {(1, 1), (-1, 1), (-1, -1), (1, -1)}

/-- `d:pattern`: all twenty slots, with a fixed transparent order. -/
def externalSlot : Fin 20 → Plane × Compass :=
  ![((1, 1), .east), ((1, 1), .north), ((-1, 1), .north), ((-1, 1), .west),
    ((-1, -1), .west), ((-1, -1), .south), ((1, -1), .south), ((1, -1), .east),
    ((2, 0), .east), ((2, 0), .north), ((2, 0), .south),
    ((0, 2), .east), ((0, 2), .north), ((0, 2), .west),
    ((-2, 0), .north), ((-2, 0), .west), ((-2, 0), .south),
    ((0, -2), .east), ((0, -2), .west), ((0, -2), .south)]

/-- `d:pattern`: finite raw data; coveredness is a separate predicate. -/
structure PatternData where
  outgoing : Compass
  status : templateSites → Status
  kept : templateSites → Finset Compass

/-- Template status, with removed values outside its finite support. -/
def PatternData.statusAt (π : PatternData) (x : Plane) : Status :=
  if h : x ∈ templateSites then π.status ⟨x, h⟩ else .X

/-- Kept half-bonds of a template site, expressed in absolute directions. -/
def PatternData.keptAt (π : PatternData) (x : Plane) : Finset Plane :=
  if h : x ∈ templateSites then (π.kept ⟨x, h⟩).image (fun d => x + d.step) else ∅

/-- `d:pattern`: the corrected covered rules, including the covering-tip exception. -/
def PatternData.Covered (π : PatternData) : Prop :=
  π.outgoing ≠ .south ∧ π.statusAt (0, 0) = .U ∧
  π.keptAt (0, 0) = {(1, 0), (0, 1), (-1, 0)} ∧
  (π.statusAt (0, -1) = .X ∨ (π.statusAt (0, -1) = .D ∧
    (π.keptAt (0, -1)).card = 2 ∧ (0, 0) ∉ π.keptAt (0, -1))) ∧
  (∀ d ∈ ({Compass.east, .north, .west} : Finset Compass),
    π.statusAt d.step = .U ∨ π.statusAt d.step = .X ∨
      (π.statusAt d.step = .D ∧ (π.keptAt d.step).card = 2 ∧ (0, 0) ∈ π.keptAt d.step)) ∧
  π.statusAt π.outgoing.step ≠ .X ∧
  (∀ x ∈ templateCorners, π.statusAt x = .U ∨ π.statusAt x = .X ∨
    (π.statusAt x = .D ∧ (π.keptAt x).card = 2)) ∧
  (∀ x ∈ templateSites, x ≠ (0, 0) → x ∉ templateTips → π.statusAt x = .U →
    π.keptAt x = neighbours x) ∧
  (∀ x ∈ templateTips, π.statusAt x = .U) ∧
  ∀ x ∈ templateSites \ templateTips, ∀ y ∈ templateSites \ templateTips,
    π.statusAt x ≠ .X → π.statusAt y ≠ .X → Adjacent x y →
      (y ∈ π.keptAt x ↔ x ∈ π.keptAt y)

/-- Present template bonds ignore any global kept set at a covering tip. -/
def PatternData.bonds (π : PatternData) : Finset (Plane × Plane) :=
  (internalBonds templateSites).filter fun e =>
    π.statusAt e.1 ≠ .X ∧ π.statusAt e.2 ≠ .X ∧
    (e.1 ∈ templateTips ∨ e.2 ∈ π.keptAt e.1) ∧
    (e.2 ∈ templateTips ∨ e.1 ∈ π.keptAt e.2)

/-- Active sites of a covered template. -/
def PatternData.active (π : PatternData) : Finset Plane :=
  templateSites.filter fun x => π.statusAt x ≠ .X

/-- Finite template spin coordinates. -/
def PatternData.spins (π : PatternData) (n : (x : π.active) → SpinLetter) (x : Plane) : Vec3 :=
  if h : x ∈ π.active then spinVector (n ⟨x, h⟩) else 0

/-- `d:pattern`: finite current/next functional. Every external slot is retained.
For next, the passage law changes to D and its out-bond is dropped. -/
def patternFunctional (π : PatternData) (next : Bool) (m : Fin 20 → UnitVector)
    (f : (Plane → Vec3) → ℝ) : ℝ :=
  ∑ n : (x : π.active) → SpinLetter,
    (∏ x : π.active,
      spinWeight (if next ∧ x.val = (0, 0) then .D else π.statusAt x.val) (n x)) *
    f (π.spins n) *
    (∏ e ∈ π.bonds,
      if next ∧ ({e.1, e.2} : Finset Plane) = {(0, 0), π.outgoing.step} then 1
      else 1 + dot (π.spins n e.1) (π.spins n e.2)) *
    ∏ j : Fin 20,
      if π.statusAt (externalSlot j).1 = .X then 1
      else 1 + dot (m j).val (π.spins n (externalSlot j).1)

/-- `d:pattern`: current covered local partition polynomial. -/
def patternCurrent (π : PatternData) (m : Fin 20 → UnitVector) : ℝ :=
  patternFunctional π false m (fun _ => 1)

/-- `d:pattern`: next covered local partition polynomial. -/
def patternNext (π : PatternData) (m : Fin 20 → UnitVector) : ℝ :=
  patternFunctional π true m (fun _ => 1)

/-- `h:H1`: pointwise inequalities; no optimality or minimizer is asserted. -/
def LocalPatternBound (cs ct : ℝ) : Prop :=
  0 < cs ∧ cs ≤ 1 ∧ 0 < ct ∧ ct ≤ 1 ∧
  ∀ π : PatternData, π.Covered → ∀ m : Fin 20 → UnitVector,
    (if π.outgoing = .north then cs else ct) * patternNext π m ≤ patternCurrent π m

end AKLT.Defs
