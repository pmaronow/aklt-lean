import Mathlib

/-! Finite lattice conventions shared by all three lanes. -/

namespace AKLT.Defs

/-- `d:moment`: the ambient plane, never a quotient in the analytic lanes. -/
abbrev Plane := ℤ × ℤ

/-- `d:moment`: ambient nearest-neighbour distance. -/
def latticeDist (x y : Plane) : ℕ := (x.1 - y.1).natAbs + (x.2 - y.2).natAbs

/-- `d:moment`: ambient maximum-coordinate distance. -/
def supDist (x y : Plane) : ℕ := max (x.1 - y.1).natAbs (x.2 - y.2).natAbs

/-- `d:memory-automaton`: absolute compass directions. -/
inductive Compass where
  | east | north | west | south
  deriving DecidableEq, Repr

instance : Fintype Compass :=
  ⟨{.east, .north, .west, .south}, by intro d; cases d <;> simp⟩

/-- The unit displacement of an absolute direction. -/
def Compass.step : Compass → Plane
  | .east => (1, 0)
  | .north => (0, 1)
  | .west => (-1, 0)
  | .south => (0, -1)

/-- Reversal of an absolute direction. -/
def Compass.reverse : Compass → Compass
  | .east => .west
  | .north => .south
  | .west => .east
  | .south => .north

/-- Nearest-neighbour adjacency, always in the ambient plane. -/
def Adjacent (x y : Plane) : Prop := latticeDist x y = 1

instance (x y : Plane) : Decidable (Adjacent x y) := inferInstanceAs (Decidable (_ = _))

/-- Four physical neighbours. -/
def neighbours (x : Plane) : Finset Plane := Finset.univ.image (fun d : Compass => x + d.step)

/-- The positive orientations, used solely to count each internal bond once. -/
def positiveNeighbours (x : Plane) : Finset Plane := {(x.1 + 1, x.2), (x.1, x.2 + 1)}

/-- `d:pinmodel`: each internal unoriented edge, indexed once. -/
def internalBonds (G : Finset Plane) : Finset (Plane × Plane) :=
  G.biUnion fun x => (positiveNeighbours x ∩ G).image (fun y => (x, y))

/-- `d:pinmodel`: original legs, before any removals. -/
def originalLegs (G : Finset Plane) : Finset (Plane × Plane) :=
  G.biUnion fun x => (neighbours x \ G).image (fun z => (x, z))

/-- `d:moment`: distance to a set, including value infinity for the empty set. -/
noncomputable def setDistance (metric : Plane → Plane → ℕ) (x : Plane)
    (S : Set Plane) : ℕ∞ := ⨅ y : S, (metric x y.val : ℕ∞)

/-- Distance to the original exterior of a finite volume. -/
noncomputable def boundaryDepth (G : Finset Plane) (x : Plane) : ℕ∞ :=
  setDistance latticeDist x {z | z ∉ G}

/-- `d:pinmodel`: the protected layer of width two in the original volume. -/
noncomputable def protectedSites (G : Finset Plane) : Finset Plane := by
  classical
  exact G.filter fun x => boundaryDepth G x ≤ 2

/-- Exponential decay at an extended natural distance; its value at infinity is zero. -/
noncomputable def decay (θ : ℝ) (r : ℕ∞) : ℝ := if r = ⊤ then 0 else θ ^ r.toNat

/-- `d:shells`: the translated physical square of integer radius `u`. -/
def square (a : Plane) (u : ℕ) : Finset Plane :=
  (Finset.Icc (a.1 - (u : ℤ)) (a.1 + u)).product
    (Finset.Icc (a.2 - (u : ℤ)) (a.2 + u))

/-- The four corner sites, including their actual translated coordinates. -/
def squareCorners (a : Plane) (u : ℕ) : Finset Plane :=
  ({a.1 - (u : ℤ), a.1 + u} : Finset ℤ).product {a.2 - (u : ℤ), a.2 + u}

/-- `d:shells`: shell spacing `u^(1/4)`, with no integer rounding. -/
noncomputable def shellSpacing (u : ℕ) : ℝ := Real.sqrt (Real.sqrt u)

/-- `d:shells`: the integer radius `floor(i s)`. -/
noncomputable def shellRadius (u : ℕ) (i : ℤ) : ℤ := ⌊(i : ℝ) * shellSpacing u⌋

/-- `d:shells`: the largest trial index, `floor(s)+1`. -/
noncomputable def lastShellIndex (u : ℕ) : ℤ := ⌊shellSpacing u⌋ + 1

/-- `d:shells`: the remaining far volume `F_i`. -/
noncomputable def farVolume (a y : Plane) (u : ℕ) (i : ℤ) : Finset Plane := by
  classical
  exact (square a u).filter fun x => ((i : ℝ) - 1) * shellSpacing u < supDist x y

/-- `d:shells`: the physical shell `D_i`. -/
noncomputable def shell (a y : Plane) (u : ℕ) (i : ℤ) : Finset Plane := by
  classical
  exact (square a u).filter fun x => (supDist x y : ℤ) = shellRadius u i

/-- `d:shells`: the part `A_i` near the exterior of the original square. -/
noncomputable def nearShell (a y : Plane) (u l₀ : ℕ) (i : ℤ) : Finset Plane := by
  classical
  exact (shell a y u i).filter fun x =>
    setDistance supDist x {z | z ∉ square a u} ≤ (l₀ : ℕ∞)

/-- `d:shells`: the physical window `B_i`. -/
noncomputable def window (a y : Plane) (u l₀ : ℕ) (i : ℤ) : Finset Plane :=
  shell a y u i \ nearShell a y u l₀ i

/-- `d:shells`: the exceptional integer indices near corner sites. -/
noncomputable def exceptionalIndices (a y : Plane) (u : ℕ) : Finset ℤ := by
  classical
  exact (Finset.Icc 2 (lastShellIndex u)).filter fun i =>
    ∃ x ∈ shell a y u i, ∃ z ∈ squareCorners a u,
      (supDist x z : ℝ) < shellSpacing u / 3

/-- `l:shellgeom`: its purely geometric size threshold. -/
def geometryThreshold (l₀ : ℕ) : ℕ := (max 16 (6 * (l₀ + 1))) ^ 4

end AKLT.Defs
