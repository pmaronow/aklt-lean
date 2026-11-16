import AKLT.Defs.FrameModel
import AKLT.Defs.FiniteNetwork

noncomputable section
open scoped BigOperators

namespace AKLT.Defs

/-- The smaller-volume boundary induced by a larger-volume configuration and its exterior. -/
def inducedBoundary (W V : Finset Plane) (η : FrameBoundary W) (σ : PlaneConfiguration W) :
    FrameBoundary V :=
  fun z => if z.val ∈ W then extendLetters σ z.val else extendBoundary η z.val

/-- `l:planeenergy`: the conditional V law inside W, with both sides indexed by actual V configurations. -/
def conditionalPlaneLaw (κ : Plane → Fin 3) (W V : Finset Plane) (η : FrameBoundary W)
    (σ : PlaneConfiguration W) : Weight (PlaneConfiguration V) :=
  marginal (conditionOn (planeLaw κ W η) (fun τ => ∀ x ∈ W \ V, extendLetters τ x = extendLetters σ x))
    (fun τ x => extendLetters τ x.val)

/-- Conditional block law on a finite torus product, indexed only by sites of U. -/
def conditionalTorusLaw (L N : AKLT.Challenge.Size) (κ : AKLT.Challenge.Site L N → Fin 3)
    (U : Finset (AKLT.Challenge.Site L N)) (σ : TorusConfiguration L N) :
    Weight (U → IcoLetter) :=
  marginal (conditionOn (torusLaw L N κ) (AgreeOutside U σ)) (fun τ x => τ x.val)

/-- The physical set corresponding to a subvolume of a finite plane product. -/
def sitesInVolume (W V : Finset Plane) : Finset W := Finset.univ.filter fun x => x.val ∈ V

/-- `l:shellgeom`: clearance for each pair of parallel sides, expressed in coordinates.
Only a shell side that actually meets the physical square is quantified. -/
def ParallelClearance (a y : Plane) (u : ℕ) (i : ℤ) : Prop :=
  ∀ axis : Fin 2, ∀ ε δ : ℤ, (ε = 1 ∨ ε = -1) → (δ = 1 ∨ δ = -1) →
    let coord := fun z : Plane => if axis = 0 then z.1 else z.2
    let b := coord y + ε * shellRadius u i
    (∃ z ∈ square a u, coord z = b ∧ (supDist z y : ℤ) = shellRadius u i) →
      shellSpacing u / 3 ≤ ((u : ℤ) + 1 - δ * (b - coord a) : ℤ)

end AKLT.Defs
