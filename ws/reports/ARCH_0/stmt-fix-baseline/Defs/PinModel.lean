import AKLT.Defs.Moment

noncomputable section
open scoped BigOperators

namespace AKLT.Defs

/-- `d:pinmodel`: independent unit pins on each original leg, even at a shared outside endpoint. -/
abbrev PinAssignment (G : Finset Plane) := (e : originalLegs G) → UnitVector

/-- Extension by zero is only an indexing convention at omitted sites. -/
def extendIcoSpins {V : Finset Plane} (n : (x : V) → IcoLetter) (x : Plane) : Vec3 :=
  if h : x ∈ V then icoVector (n ⟨x, h⟩) else 0

/-- `d:pinmodel`: partition sum with original pins and no new factors into removed sites. -/
def pinnedSum (G Y : Finset Plane) (τ : PinAssignment G)
    (f : (Plane → Vec3) → ℝ) : ℝ :=
  ∑ n : (↥(G \ Y) → IcoLetter),
    (1 / 12 : ℝ) ^ (G \ Y).card * f (extendIcoSpins n) *
    (∏ e ∈ internalBonds (G \ Y), (1 + dot (extendIcoSpins n e.1) (extendIcoSpins n e.2))) *
    ∏ e : originalLegs G,
      if e.val.1 ∈ G \ Y then 1 + dot (τ e).val (extendIcoSpins n e.val.1) else 1

/-- `d:pinmodel`: free partition sum, omitting all original-leg factors. -/
def freeSum (G Y : Finset Plane) (f : (Plane → Vec3) → ℝ) : ℝ :=
  ∑ n : (↥(G \ Y) → IcoLetter),
    (1 / 12 : ℝ) ^ (G \ Y).card * f (extendIcoSpins n) *
    ∏ e ∈ internalBonds (G \ Y), (1 + dot (extendIcoSpins n e.1) (extendIcoSpins n e.2))

/-- `d:pinmodel`: normalized pinned expectation. -/
def pinnedExpectation (G Y : Finset Plane) (τ : PinAssignment G)
    (f : (Plane → Vec3) → ℝ) : ℝ := pinnedSum G Y τ f / pinnedSum G Y τ (fun _ => 1)

/-- `d:pinmodel`: normalized free expectation. -/
def freeExpectation (G Y : Finset Plane) (f : (Plane → Vec3) → ℝ) : ℝ :=
  freeSum G Y f / freeSum G Y (fun _ => 1)

/-- `d:pinmodel`: pinned/free partition ratio, always relative to the original G. -/
def partitionRatio (G Y : Finset Plane) (τ : PinAssignment G) : ℝ :=
  pinnedSum G Y τ (fun _ => 1) / freeSum G Y (fun _ => 1)

/-- `h:P`: all original volumes, independent unit pins, permitted removals and distance-two pairs.
Distances are to the original protected layer, and infinity has decay zero. -/
def ResponseProperty (A θ : ℝ) : Prop :=
  2 ≤ A ∧ 0 < θ ∧ θ < 1 ∧
  ∀ G : Finset Plane, ∀ τ : PinAssignment G, ∀ Y : Finset Plane,
    Y ⊆ G \ protectedSites G → ∀ u v : Plane,
    u ∈ G \ Y → v ∈ G \ Y → latticeDist u v = 2 →
    (∃ c ∈ Y, Adjacent u c ∧ Adjacent v c) →
    |pinnedExpectation G Y τ (fun n => dot (n u) (n v)) -
      freeExpectation G Y (fun n => dot (n u) (n v))| ≤
      A * decay θ (min (setDistance latticeDist u (↑(protectedSites G) : Set Plane))
        (setDistance latticeDist v (↑(protectedSites G) : Set Plane)))

/-- `t:cutMOS`: the exact removal-cost constant, including the retained seed. -/
def cutCost (A θ : ℝ) : ℝ :=
  1 + 4 * A + 10 * A * θ ^ (-4 : ℤ) *
    (48 * θ ^ (14 : ℕ) * (17 + 1 / (1 - θ)) + 1)

/-- `t:cutMOS`: the displayed common minorization probability. -/
def cutProbability (A θ : ℝ) : ℝ := Real.exp (-2 * cutCost A θ)

end AKLT.Defs
