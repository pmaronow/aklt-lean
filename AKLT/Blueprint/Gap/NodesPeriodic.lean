module
public import AKLT.Blueprint.Gap.NodesShell

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
set_option maxHeartbeats 800000
open scoped BigOperators
open AKLT.Defs AKLT.Challenge
attribute [local instance] Classical.propDecidable
namespace AKLT.Blueprint.Gap
local instance (α : Type) : DecidableEq α := Classical.decEq α

/-- `t:periodic`, sec4:339-346. Centres containing x are x-z for the offset square;
coordinate reduction is injective since 2M < L,N. Labels, rather than distinct sets,
are counted. -/
def ContainingBlockCountStatement : Prop :=
  ∀ (L N : Size) M, 1 ≤ M → 2*M+3 ≤ L.val → 2*M+3 ≤ N.val →
    ∀ x, (Finset.univ.filter fun a => x ∈ torusSquare L N M a).card = volumeCount M

/-- `t:periodic`, sec4:347-359. The full halo is the offset square of radius M+1.
Its coordinate differences are ≤2M+2, still strictly less than each period; subtract
the inner count. This includes all four corner offsets and equality L=2M+3. -/
def ExteriorBlockCountStatement : Prop :=
  ∀ (L N : Size) M, 1 ≤ M → 2*M+3 ≤ L.val → 2*M+3 ≤ N.val →
    ∀ x, (Finset.univ.filter fun a => x ∈ torusHalo L N M a \ torusSquare L N M a).card = haloCount M

/-- `t:periodic`, sec4:382-384. The offset injection bounds block volume by the
number of labels A=LN. No symmetry or invariance of the measure is used. -/
def BlockVolumeBoundStatement : Prop :=
  ∀ (L N : Size) M, 1 ≤ M → 2*M+3 ≤ L.val → 2*M+3 ≤ N.val →
    volumeCount M ≤ Fintype.card (Site L N)

/-- `t:periodic`, sec4:362-381. Same uniformly chosen label: erase the changed
site in containing blocks, incur at most 1+K on adjacent exterior blocks, and use
identical resampling elsewhere. Sum the three costs using the exact label counts. -/
def PeriodicNeighbourCouplingStatement : Prop :=
  ∀ (L N : Size) (S : Site L N → Type) [∀ x, Fintype (S x)] [∀ x, Nonempty (S x)]
    (μ : Weight (Config S)), PositiveProbability μ →
    ∀ M K, 1 ≤ M → 0 ≤ K → PeriodicCounts L N M → TorusRangeOne μ M → BlockInfluence μ M K →
    ∀ σ τ, hamming σ τ = 1 →
      ∃ c : Coupling (blockAverage μ (torusSquare L N M) σ) (blockAverage μ (torusSquare L N M) τ),
        couplingCost c ≤ 1 - ((volumeCount M : ℝ) - (haloCount M : ℝ)*K) / Fintype.card (Site L N)

/-- `t:periodic`, sec4:396-402. The exact ratio equals (1/500)(1-1/(2M+1)^2)
at K=M/1000. Cross-multiply positive denominators; M≥1 prevents degenerate division. -/
def PeriodicBudgetStatement : Prop :=
  ∀ M : ℕ, 1 ≤ M →
    0 < (volumeCount M : ℝ) ∧
    0 < (volumeCount M : ℝ) - (haloCount M : ℝ)*((M : ℝ)/1000) ∧
    (499/500 : ℝ) ≤ 1 - (haloCount M : ℝ)*((M : ℝ)/1000)/(volumeCount M : ℝ)

/-- `l:colour`, PLAN:664-689; sec4:428-438. Verify adjacent residues for the
explicit odd/even cycle formula, including the wrap edge at period three. -/
def TorusColourStatement : Prop :=
  ∀ L N : Size, ProperTorusColouring (torusColour L N)

/-- `t:mainW`, sec4:442-444. Every plane edge reduces to one of the frozen torus
bonds, perhaps with reversed orientation; Size ensures distinct endpoints. -/
def PullbackColourStatement : Prop :=
  ∀ (L N : Size) (κ : Site L N → Fin 3), ProperTorusColouring κ →
    ProperPlaneColouring (κ ∘ reduction L N)

/-- `l:boxlift`, PLAN:877-885; sec4:448-450. Lift to one physical square plus its
halo. Modulo-period differences have absolute value ≤2M+2, hence vanish as integers. -/
def HaloInjectionStatement : Prop :=
  ∀ (L N : Size) M, 1 ≤ M → 2*M+3 ≤ L.val → 2*M+3 ≤ N.val →
    ∀ a : Plane, Set.InjOn (reduction L N) (↑(square a (M+1)) : Set Plane)

/-- Exact local graph data for a lifted square, used by the gauge construction.
Internal and crossing bonds are represented by unordered endpoint sets. -/
def LiftBonds (L N : Size) (M : ℕ) (a : Plane) : Prop :=
  let Q := (square a M).image (reduction L N)
  (∀ x y, x ∈ square a M → y ∈ square a M →
    (Adjacent x y ↔ ∃ e : Bond L N, bondSites e = {reduction L N x, reduction L N y})) ∧
  (∀ e : Bond L N, (bondSites e ∩ Q).card = 1 →
    ∃ x ∈ square a M, ∃ y ∈ square a (M+1) \ square a M,
      Adjacent x y ∧ bondSites e = {reduction L N x, reduction L N y}) ∧
  (∀ x ∈ square a (M+1), reduction L N x ∈ Q ↔ x ∈ square a M)

/-- `l:boxlift`, PLAN:879-885; sec4:448-450,476-480. Internal and crossing bonds
correspond exactly; the injective halo prevents any exterior image becoming internal. -/
def LiftBondStatement : Prop :=
  ∀ (L N : Size) M, 1 ≤ M → 2*M+3 ≤ L.val → 2*M+3 ≤ N.val →
    ∀ a : Plane, Set.InjOn (reduction L N) (↑(square a (M+1)) : Set Plane) → LiftBonds L N M a

/-- The sign uses lifted integer coordinates, never a torus representative. -/
def paritySign (z : Plane) : ℝ := if Even (z.1 + z.2) then 1 else -1

/-- Coordinate part of l:boxlift, before any probability-law identity. -/
structure BoxCoordinates (L N : Size) (M : ℕ) (a : Site L N) (κ : Site L N → Fin 3) where
  centre : Plane
  centre_reduces : reduction L N centre = a
  change : ProductChange (fun _ : torusSquare L N M a => IcoLetter)
    (fun _ : square centre M => IcoLetter)
  site_reduces : ∀ x, reduction L N (change.sites x).val = x.val
  vector_change : ∀ ω x, frameVector (κ x.val) (change.configurations ω (change.sites x)) =
    paritySign (change.sites x).val • frameVector (κ x.val) (ω x)
  boundary : TorusConfiguration L N → Config (fun _ : Plane => IcoLetter)
  boundary_vector : ∀ σ z, z ∈ exteriorSites (square centre M) →
    frameVector (κ (reduction L N z)) (boundary σ z) =
      paritySign z • frameVector (κ (reduction L N z)) (σ (reduction L N z))
  boundary_change : ∀ y, y ∈ torusHalo L N M a \ torusSquare L N M a →
    ∀ σ τ, AgreeOutside {y} σ τ → ∃ z : Plane,
      z ∉ square centre M ∧ setDistance supDist z (↑(square centre M) : Set Plane) = 1 ∧
      ∀ w, w ≠ z → boundary σ w = boundary τ w

/-- `l:boxlift`, PLAN:886-901; sec4:451-463,478-486 (coordinates). Injectivity and
antipodality define a permutation in each site alphabet; choose a lift of the centre,
and use halo injectivity for the unique changed exterior site. -/
def BoxCoordinatesStatement : Prop :=
  (∀ j : Fin 3, Function.Injective (frameVector j) ∧
    ∀ a, ∃ b, frameVector j b = -frameVector j a) →
  ∀ (L N : Size) M, 1 ≤ M → 2*M+3 ≤ L.val → 2*M+3 ≤ N.val →
    (∀ a : Plane, Set.InjOn (reduction L N) (↑(square a (M+1)) : Set Plane)) →
    ∀ κ : Site L N → Fin 3, ∀ a : Site L N, Nonempty (BoxCoordinates L N M a κ)

/-- `l:boxlift`, PLAN:886-901; sec4:451-463 (weights). Adjacent lifted parity
signs are opposite. Group the internal/crossing factors by the exact bond lift and
cancel the positive exterior-only factors in the conditional normalisation. -/
def BoxGaugeLawStatement : Prop :=
  (∀ i j : Fin 3, i ≠ j → ∀ a b : IcoLetter,
    0 < 1 + dot (frameVector i a) (frameVector j b) ∧
    0 < 1 - dot (frameVector i a) (frameVector j b)) →
  ∀ (L N : Size) M, 1 ≤ M → 2*M+3 ≤ L.val → 2*M+3 ≤ N.val →
    ∀ κ : Site L N → Fin 3, ProperTorusColouring κ → ∀ a,
    ∀ C : BoxCoordinates L N M a κ, LiftBonds L N M C.centre →
    ∀ σ, Carries C.change (blockLaw (torusLaw L N κ) (torusSquare L N M a) σ)
      ((frameSpec (κ ∘ reduction L N)).law (square C.centre M) (C.boundary σ))

/-- `t:mainW`, sec4:440-441. The four nearest neighbours belong to the full
one-neighbourhood halo. The local Markov input from planeenergy therefore implies
the sup-distance-one version required by the periodic criterion. -/
def TorusRangeTransferStatement : Prop :=
  ∀ (L N : Size) (κ : Site L N → Fin 3),
    (∀ U σ τ, (∀ z ∈ (U.biUnion torusNeighbours) \ U, σ z = τ z) →
      conditionalTorusLaw L N κ U σ = conditionalTorusLaw L N κ U τ) →
    ∀ M, 1 ≤ M → TorusRangeOne (torusLaw L N κ) M

/-- `t:mainW`, sec4:464-469. Count horizontal and vertical internal bonds once:
2M per row/column and 2M+1 rows/columns. The M=0 empty-edge case is included. -/
def SquareInternalEdgesStatement : Prop :=
  ∀ a M, (internalBonds (square a M)).card = internalCount M

/-- `l:planeenergy` used in `t:mainW`, sec4:415-417 (consistency). Convert finite
boundaries to total assignments and prove plane range one directly from the four
nearest-neighbour weight factors. -/
def FrameSpecRegularityStatement : Prop :=
  ∀ κ : Plane → Fin 3, ProperPlaneColouring κ →
  (∀ W η, PositiveProbability (planeLaw κ W η)) →
  (∀ W V, V ⊆ W → ∀ η σ,
    conditionalPlaneLaw κ W V η σ = planeLaw κ V (inducedBoundary W V η σ)) →
    RegularSpec (frameSpec κ)

/-- `l:planeenergy` used in `t:mainW`, sec4:415-417 (finite energy). Reindex the
prescribed and conditioning sites by their inclusions in W; the assignment exponent
is the cardinal of the prescribed sites, not that of the conditioning sites. -/
def FrameSpecEnergyStatement : Prop :=
  ∀ κ : Plane → Fin 3,
  (∀ W η, ∀ U J : Finset Plane, U ⊆ W → J ⊆ W → Disjoint U J →
    ∀ a b : Plane → IcoLetter,
      frameEnergy^U.card ≤ conditionalProbability (planeLaw κ W η)
        (fun σ => ∀ x ∈ J, extendLetters σ x = a x)
        (fun σ => ∀ x ∈ U, extendLetters σ x = b x)) →
    SpecEnergy (frameSpec κ) frameEnergy

/-- `d:W`/`t:mainW`, sec4:414-417. Restrict total exterior assignments to the
finite nearest-neighbour boundary. Since B⊆F, extending a sample off F has no effect. -/
def FrameWindowTransferStatement : Prop :=
  ∀ l p Mstar, WindowProperty l p Mstar → ∀ κ : Plane → Fin 3,
    ProperPlaneColouring κ → SpecWindow (frameSpec κ) l p Mstar

end AKLT.Blueprint.Gap
