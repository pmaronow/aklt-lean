module
public import AKLT.Defs.Domain

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators

namespace AKLT.Defs

/-- `h:H1`: the two frozen rational local thresholds. -/
def localThreshold : Bool → ℚ := fun straight => if straight then 961 / 1000 else 187 / 200

/-- `d:weights`: the inverse local threshold. -/
def passageFactor (straight : Bool) : ℚ := (localThreshold straight)⁻¹

/-- `l:log-mean-bounds`: the adopted exact alpha table; turn alpha is 150000/10^6. -/
def alphaBound (straight : Bool) : ℚ := if straight then 145217 / 10^6 else 150000 / 10^6

/-- `l:log-mean-bounds`: the adopted exact beta table. -/
def betaBound (straight : Bool) : ℚ := if straight then 352782 / 10^6 else 357549 / 10^6

/-- `l:log-mean-bounds`: the one-live-neighbour beta-prime table. -/
def betaPrimeBound (straight : Bool) : ℚ := if straight then 340008 / 10^6 else 344661 / 10^6

/-- `d:weights`: a finite direction word; there is no spatial quotient. -/
abbrev DirectionWord (n : ℕ) := Fin n → Compass

/-- The j-th vertex of a word, with a clamped natural index for convenient prefix definitions. -/
def wordVertex {n : ℕ} (u : Plane) (w : DirectionWord n) (j : ℕ) : Plane :=
  u + ∑ i : Fin n, if i.val < j then (w i).step else 0

/-- The unoriented edge at a departure. -/
def wordBond {n : ℕ} (u : Plane) (w : DirectionWord n) (i : Fin n) : Finset Plane :=
  {wordVertex u w i.val, wordVertex u w (i.val + 1)}

/-- `d:weights`: distinct unoriented bonds and the forbidden initial reversal. -/
def IsTrail {n : ℕ} (u : Plane) (incoming : Compass) (w : DirectionWord n) : Prop :=
  Function.Injective (wordBond u w) ∧ ∀ i : Fin n, i.val = 0 → w i ≠ incoming.reverse

/-- Incoming direction at a departure, including the designated virtual first bond. -/
def wordIncoming {n : ℕ} (incoming : Compass) (w : DirectionWord n) (i : Fin n) : Compass :=
  if h : i.val = 0 then incoming else w ⟨i.val - 1, by omega⟩

/-- A straight departure compares actual outgoing and incoming directions. -/
def wordStraight {n : ℕ} (incoming : Compass) (w : DirectionWord n) (i : Fin n) : Bool :=
  decide (w i = wordIncoming incoming w i)

/-- Departure count before index i; arrivals alone do not count as revisits. -/
def departureCount {n : ℕ} (u : Plane) (w : DirectionWord n) (i : ℕ) (x : Plane) : ℕ :=
  ((Finset.range (min i n)).filter fun j => wordVertex u w j = x).card

/-- `d:weights`: true revisit means a previous departure from the same site. -/
def wordRevisit {n : ℕ} (u : Plane) (w : DirectionWord n) (i : Fin n) : Bool :=
  decide (0 < departureCount u w i.val (wordVertex u w i.val))

/-- `d:weights`: the true lattice trail weight, including the revisit factor 1/5. -/
def trailWeight {n : ℕ} (u : Plane) (incoming : Compass) (w : DirectionWord n) : ℚ :=
  ∏ i, if wordRevisit u w i then 1 / 5 else passageFactor (wordStraight incoming w i) / 3

/-- The mass-free coefficient before exposure products, equal to 3^-n(3/5)^rev. -/
def trailBaseWeight {n : ℕ} (u : Plane) (w : DirectionWord n) : ℚ :=
  ∏ i, if wordRevisit u w i then 1 / 5 else 1 / 3

/-- `h:H2`: every finite-length sum, with arbitrary start and designated incoming direction. -/
def OpenTrailBound (CV q : ℝ) : Prop := by
  classical
  exact
  1 ≤ CV ∧ 0 < q ∧ q < 1 ∧
  ∀ n : ℕ, ∀ u : Plane, ∀ incoming : Compass,
    (∑ w : DirectionWord n, if IsTrail u incoming w then (trailWeight u incoming w : ℝ) else 0) ≤
      CV * q ^ n

/-- `t:inputs`: the selected exact memory-six rate. -/
def certifiedRate : ℚ := 1119948287353 / 1120437614225

/-- A vertex-list view of a finite word for the network trace. -/
def wordVertices {n : ℕ} (u : Plane) (w : DirectionWord n) : List Plane :=
  (List.range (n + 1)).map (wordVertex u w)

/-- `d:trace`: finite stopped trails of present distinct bonds, with no departure from S.
The original finite bond set bounds the length, so this class is finitely enumerable. -/
def StoppedNetworkTrail {G : Finset Plane} {n : ℕ} (D : Network G) (u : Plane)
    (T : Finset Plane) (w : DirectionWord n) : Prop :=
  Function.Injective (wordBond u w) ∧
  (∀ i : Fin n, D.Present (wordVertex u w i.val) (wordVertex u w (i.val + 1))) ∧
  (∀ j < n, wordVertex u w j ∉ T ∧ wordVertex u w j ∉ protectedSites G) ∧
  wordVertex u w n ∈ T

/-- `d:trace`: each fixed-length part of T_D(u,T), generated directly from direction words. -/
def stoppedNetworkTrails {G : Finset Plane} (D : Network G) (u : Plane) (T : Finset Plane)
    (n : ℕ) : Finset (DirectionWord n) := by
  classical
  exact Finset.univ.filter (StoppedNetworkTrail D u T)

/-- `p:pairwalk`: precisely the target degree restriction, including original legs. -/
def AdmissibleTarget {G : Finset Plane} (D : Network G) (v : Plane) : Prop :=
  v ∈ D.active ∧
    ((D.status v = .U ∧ (D.presentNeighbours v).card +
      ((originalLegs G).filter fun e => e.1 = v).card ≤ 3) ∨
    (D.status v = .D ∧ (D.presentNeighbours v).card ≤ 1))

end AKLT.Defs
