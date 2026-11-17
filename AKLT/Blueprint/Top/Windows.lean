module
public import AKLT.Blueprint.Top.Quantum
public import AKLT.Blueprint.Top.Response

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open AKLT.Defs

namespace AKLT.Blueprint.Top

/-- `l:shellgeom`: the shared purely geometric export, including parallel-side clearance
and the predecessor-shell separation, with all translates and admissible exterior seeds. -/
def ShellGeometryStatement : Prop :=
  ∀ l₀ : ℕ, 1 ≤ l₀ → ∀ a y : Plane, ∀ u : ℕ, geometryThreshold l₀ ≤ u →
    setDistance supDist y (↑(square a u) : Set Plane) = 1 →
    (exceptionalIndices a y u).card ≤ 1 ∧
    (∀ i : ℤ, 2 ≤ i → i ≤ lastShellIndex u → shell a y u i ⊆ farVolume a y u i) ∧
    (∀ i : ℤ, 2 ≤ i → i ≤ lastShellIndex u → i ∉ exceptionalIndices a y u →
      (nearShell a y u l₀ i).card ≤ 8 * l₀ ∧ ParallelClearance a y u i) ∧
    ∀ i : ℤ, 2 ≤ i →
      (∀ x ∈ square a u \ farVolume a y u i,
        setDistance supDist x (↑(farVolume a y u i) : Set Plane) ≤ 1 → x ∈ shell a y u (i - 1)) ∧
      ¬ setDistance supDist y (↑(farVolume a y u i) : Set Plane) ≤ 1

/-- `t:cutMOS`: P implies W for the actual frame family, with l0=64 and exactly
the displayed exp(-2E); one common threshold works for every colouring and translate. -/
def CutMOSStatement : Prop :=
  ∀ A θ : ℝ, ResponseProperty A θ →
    ∃ Mstar : ℕ, WindowProperty 64 (cutProbability A θ) Mstar

/-- `t:mainW`: existence of any uniform window parameters gives the eventual
all-parity frozen quantum conclusion. Small-volume uniqueness is a separate algebraic input. -/
def MainWStatement : Prop :=
  (∃ l₀ : ℕ, ∃ p₀ : ℝ, ∃ Mstar : ℕ, WindowProperty l₀ p₀ Mstar) → EventualMain

end AKLT.Blueprint.Top
