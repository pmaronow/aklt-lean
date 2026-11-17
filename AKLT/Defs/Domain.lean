module
public import AKLT.Defs.PinModel

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators

namespace AKLT.Defs

/-- `d:domain`: status and kept sets on an original finite G. No mass field is present.
Validity is an explicit predicate, so an auxiliary terminal network is never silently ordinary. -/
structure Network (G : Finset Plane) where
  status : Plane → Status
  kept : Plane → Finset Plane

/-- `d:domain`: nonremoved sites of the original volume. -/
def Network.active {G : Finset Plane} (D : Network G) : Finset Plane :=
  G.filter fun x => D.status x ≠ .X

/-- A bond is present exactly when both active endpoints keep it. -/
def Network.Present {G : Finset Plane} (D : Network G) (x y : Plane) : Prop :=
  x ∈ D.active ∧ y ∈ D.active ∧ Adjacent x y ∧ y ∈ D.kept x ∧ x ∈ D.kept y

instance {G : Finset Plane} (D : Network G) (x y : Plane) : Decidable (D.Present x y) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

/-- The finite set of present bonds, each counted once. -/
def Network.bonds {G : Finset Plane} (D : Network G) : Finset (Plane × Plane) :=
  (internalBonds G).filter fun e => D.Present e.1 e.2

/-- Present degree counts actual bonds, not merely kept half-edges. -/
def Network.presentNeighbours {G : Finset Plane} (D : Network G) (x : Plane) : Finset Plane :=
  (neighbours x).filter fun y => D.Present x y

/-- Common local restrictions for ordinary and auxiliary networks. -/
def Network.LocalRules {G : Finset Plane} (D : Network G) : Prop :=
  (∀ x, x ∉ G → D.status x = .X) ∧
  (∀ x, D.kept x ⊆ neighbours x ∩ G) ∧
  (∀ x ∈ G, D.status x = .D → (D.presentNeighbours x).card ≤ 2) ∧
  (∀ x ∈ D.active, (D.presentNeighbours x).card +
    ((originalLegs G).filter fun e => e.1 = x).card ≤ 4)

/-- `d:domain`: an ordinary domain protects original S(G), including all its kept bonds. -/
def Network.Ordinary {G : Finset Plane} (D : Network G) : Prop :=
  D.LocalRules ∧ ∀ x ∈ protectedSites G,
    D.status x = .U ∧ D.kept x = neighbours x ∩ G

/-- `d:domain`: auxiliary networks permit protected kept-set defects, retaining all original legs. -/
def Network.Auxiliary {G : Finset Plane} (D : Network G) : Prop :=
  D.LocalRules ∧ ∀ x ∈ protectedSites G, D.status x = .U

/-- `d:domain`: the ordinary consistent class, including the corrected mutual-kept rule. -/
def Network.Consistent {G : Finset Plane} (D : Network G) : Prop :=
  D.Ordinary ∧
  (∀ x ∈ G, D.status x = .U → D.kept x = neighbours x ∩ G) ∧
  (∀ x ∈ G, D.status x = .D → (D.kept x).card = 2) ∧
  ∀ x ∈ D.active, ∀ y ∈ D.active, Adjacent x y → (y ∈ D.kept x ↔ x ∈ D.kept y)

/-- Spin coordinates on the active sites, extended only for indexing at removed sites. -/
def Network.spins {G : Finset Plane} (D : Network G)
    (n : (x : D.active) → SpinLetter) (x : Plane) : Vec3 :=
  if h : x ∈ D.active then spinVector (n ⟨x, h⟩) else 0

/-- `d:domain`: finite partition functional, with every surviving original leg retained. -/
def Network.partition {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (pinned : Bool) (f : (Plane → Vec3) → ℝ) : ℝ :=
  ∑ n : (x : D.active) → SpinLetter,
    (∏ x : D.active, spinWeight (D.status x.val) (n x)) * f (D.spins n) *
    (∏ e ∈ D.bonds, (1 + dot (D.spins n e.1) (D.spins n e.2))) *
    ∏ e : originalLegs G,
      if pinned = true ∧ e.val.1 ∈ D.active then
        1 + dot (τ e).val (D.spins n e.val.1) else 1

/-- `d:domain`: normalized expectation in either the pinned or free network. -/
def Network.expectation {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (pinned : Bool) (f : (Plane → Vec3) → ℝ) : ℝ :=
  D.partition τ pinned f / D.partition τ pinned (fun _ => 1)

/-- `d:domain`: pinned/free partition ratio, with unchanged original G and pins. -/
def Network.ratio {G : Finset Plane} (D : Network G) (τ : PinAssignment G) : ℝ :=
  D.partition τ true (fun _ => 1) / D.partition τ false (fun _ => 1)

/-- `d:trace`: only the two admissible start cases used in the proof. -/
def Network.AdmissibleStart {G : Finset Plane} (D : Network G) (u : Plane) : Prop :=
  u ∈ D.active ∧ u ∉ protectedSites G ∧
    ((D.status u = .U ∧ (D.presentNeighbours u).card ≤ 3) ∨
      (D.status u = .D ∧ (D.presentNeighbours u).card ≤ 1))

/-- `d:trace`: drop the traversed bond at both ends, then U becomes D and D becomes X. -/
def traceStep {G : Finset Plane} (D : Network G) (y o : Plane) : Network G where
  status := Function.update D.status y (if D.status y = .U then .D else .X)
  kept := fun x => if x = y then (D.kept x).erase o
    else if x = o then (D.kept x).erase y else D.kept x

/-- `d:trace`: the trace along a finite vertex list, including the length-zero convention. -/
def traceNetwork {G : Finset Plane} (D : Network G) : List Plane → Network G
  | y :: o :: rest => traceNetwork (traceStep D y o) (o :: rest)
  | _ => D

/-- `d:trace`: mass-free coefficient, recording status at departure in the evolving network. -/
def traceCoefficient {G : Finset Plane} (D : Network G) : List Plane → ℚ
  | y :: o :: rest => (if D.status y = .U then 1 / 3 else if D.status y = .D then 1 / 5 else 0) *
      traceCoefficient (traceStep D y o) (o :: rest)
  | _ => 1

/-- `d:trace`: the partition ratio along a traced path, for either pin choice. -/
def traceRatio {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (pinned : Bool) (w : List Plane) : ℝ :=
  (traceNetwork D w).partition τ pinned (fun _ => 1) / D.partition τ pinned (fun _ => 1)

/-- `d:pairenv`: the two pair types, collinear B and diagonal C. -/
inductive PairType where
  | B | C
  deriving DecidableEq, Repr

instance : Fintype PairType := ⟨{.B, .C}, by intro X; cases X <;> simp⟩

/-- `d:pairenv`: endpoint geometry, with all distances ambient. -/
def HasPairType (X : PairType) (u v : Plane) : Prop :=
  latticeDist u v = 2 ∧ (if X = .B then u.1 = v.1 ∨ u.2 = v.2 else u.1 ≠ v.1 ∧ u.2 ≠ v.2)

/-- `d:pairenv`: the ordinary response-pair class with its designated removed center. -/
def Network.ResponsePair {G : Finset Plane} (D : Network G) (X : PairType)
    (u v c : Plane) : Prop :=
  D.Consistent ∧ u ∈ D.active ∧ v ∈ D.active ∧ c ∈ G ∧ D.status c = .X ∧
  Adjacent u c ∧ Adjacent v c ∧ HasPairType X u v ∧
  (D.status u = .U ∨ (D.status u = .D ∧ (D.presentNeighbours u).card ≤ 1)) ∧
  (D.status v = .U ∨ (D.status v = .D ∧ (D.presentNeighbours v).card ≤ 1))

/-- `d:pairenv`: bounded ordinary-domain response envelope, never over auxiliary networks. -/
def responseEnvelope (X : PairType) (d : ℤ) : ℝ :=
  sSup ({0} ∪ {r | ∃ G : Finset Plane, ∃ τ : PinAssignment G, ∃ D : Network G,
    ∃ u v c : Plane, D.ResponsePair X u v c ∧
    (d.toNat : ℕ∞) ≤ min (setDistance latticeDist u (↑(protectedSites G) : Set Plane))
      (setDistance latticeDist v (↑(protectedSites G) : Set Plane)) ∧
    r = |D.expectation τ true (fun n => dot (n u) (n v)) -
      D.expectation τ false (fun n => dot (n u) (n v))|})

end AKLT.Defs
