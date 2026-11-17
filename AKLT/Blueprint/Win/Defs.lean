module
public import AKLT.Blueprint.Top.Windows

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

/-! Concrete data for §5 and Appendix B. No field of a data definition is an
unproved global statement. Distances and pins retain their original volume. -/

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.Blueprint.Win

def ShellSetup (l : ℕ) (a y : Plane) (u : ℕ) : Prop :=
  1 ≤ l ∧ geometryThreshold l ≤ u ∧
    setDistance supDist y (↑(square a u) : Set Plane) = 1

def CutSetup (a y : Plane) (u : ℕ) (i : ℤ) : Prop :=
  ShellSetup 64 a y u ∧ 2 ≤ i ∧ (i : ℝ) ≤ shellSpacing u ∧
    i ∉ exceptionalIndices a y u

def StarAdjacent (x y : Plane) : Prop := supDist x y = 1

def JoinedIn {α : Type*} (R : α → α → Prop) (S : Set α) (x y : α) : Prop :=
  Relation.ReflTransGen (fun v w => v ∈ S ∧ w ∈ S ∧ R v w) x y

def ConnectedIn {α : Type*} (R : α → α → Prop) (S : Set α) : Prop :=
  S.Nonempty ∧ ∀ x ∈ S, ∀ y ∈ S, JoinedIn R S x y

def starBall (x : Plane) : Finset Plane :=
  (Finset.Icc (x.1 - 1) (x.1 + 1)).product (Finset.Icc (x.2 - 1) (x.2 + 1))

def cross (x : Plane) : Finset Plane := insert x (neighbours x)

def rawBoundary (U : Finset Plane) : Finset Plane :=
  (U.biUnion starBall) \ U

def thicken (X₀ : Finset Plane) : Finset Plane := X₀.biUnion cross

def squareDepth (a : Plane) (u : ℕ) (z : Plane) : ℤ :=
  max 0 ((u : ℤ) + 1 - (supDist z a : ℤ))

def radialOffset (y : Plane) (u : ℕ) (i : ℤ) (z : Plane) : ℕ :=
  ((supDist z y : ℤ) - shellRadius u i).natAbs

def taper (a y : Plane) (u : ℕ) (i : ℤ) : Finset Plane := by
  classical
  exact (square a u).filter fun z =>
    (radialOffset y u i z : ℝ) ≤ shellSpacing u / 12 ∧
    (radialOffset y u i z : ℤ) + 32 ≤ squareDepth a u z

def core (a y : Plane) (u : ℕ) (i : ℤ) : Finset Plane := by
  classical
  exact (square a u).filter fun z =>
    (supDist z y : ℤ) = shellRadius u i ∧ 32 ≤ squareDepth a u z

def cutVolume (a y : Plane) (u : ℕ) (i : ℤ) : Finset Plane :=
  farVolume a y u i \ window a y u 64 i

def cutRaw (a y : Plane) (u : ℕ) (i : ℤ) : Finset Plane :=
  rawBoundary (taper a y u i)

def cutSet (a y : Plane) (u : ℕ) (i : ℤ) : Finset Plane :=
  thicken (cutRaw a y u i)

def insidePiece (a y : Plane) (u : ℕ) (i : ℤ) : Finset Plane :=
  (taper a y u i \ window a y u 64 i) \ cutSet a y u i

def outsidePiece (a y : Plane) (u : ℕ) (i : ℤ) : Finset Plane :=
  cutVolume a y u i \ (taper a y u i ∪ cutSet a y u i)

def nearCost (θ : ℝ) : ℝ := 48 * θ ^ 14 * (17 + 1 / (1 - θ))

def pairSum (V : Finset Plane) (n : Plane → Vec3) : ℝ :=
  (1 / 2) * ∑ v ∈ V, ∑ w ∈ V, if v = w then 0 else dot (n v) (n w)

def quartic (x : Plane) (n : Plane → Vec3) : ℝ :=
  let e := n (x + Compass.east.step)
  let w := n (x + Compass.west.step)
  let s := n (x + Compass.south.step)
  let t := n (x + Compass.north.step)
  dot e w * dot s t + dot e s * dot w t + dot e t * dot w s

def removalPolynomial (x : Plane) (V : Finset Plane) (n : Plane → Vec3) : ℝ :=
  1 + pairSum V n / 3 + if V.card = 4 then quartic x n / 15 else 0

def partSum (pinned : Bool) (G Y : Finset Plane) (τ : PinAssignment G)
    (f : (Plane → Vec3) → ℝ) : ℝ :=
  if pinned then pinnedSum G Y τ f else freeSum G Y f

def partMean (pinned : Bool) (G Y : Finset Plane) (τ : PinAssignment G)
    (f : (Plane → Vec3) → ℝ) : ℝ :=
  partSum pinned G Y τ f / partSum pinned G Y τ (fun _ => 1)

def logRatio (G Y : Finset Plane) (τ : PinAssignment G) : ℝ :=
  Real.log (partitionRatio G Y τ)

def NoBond (S T : Set Plane) : Prop := ∀ x ∈ S, ∀ y ∈ T, ¬ Adjacent x y

/-- All hypotheses of l:cut, including the absence of exterior legs from B. -/
def SeparatingCut (F B X G₁ G₂ : Finset Plane) : Prop :=
  B ⊆ F ∧ NoBond (↑B) {z | z ∉ F} ∧ X ⊆ F \ B ∧
  Disjoint G₁ G₂ ∧ G₁ ∪ G₂ = (F \ B) \ X ∧
  NoBond (↑G₁) (↑G₂) ∧ NoBond (↑G₁) {z | z ∉ F} ∧ NoBond (↑G₂) (↑B)

/-- Pins for G=F\B use actual frame vectors on all original legs of G. -/
def cutPins (κ : Plane → Fin 3) (G F B : Finset Plane)
    (unit : ∀ j a, normSq (frameVector j a) = 1)
    (η : FrameBoundary F) (s : PlaneConfiguration B) : PinAssignment G :=
  fun e => ⟨frameVector (κ e.val.2)
    (if e.val.2 ∈ B then extendLetters s e.val.2 else extendBoundary η e.val.2),
    unit _ _⟩

/-- Original-leg restriction: holes create no factors. A component H is obtained
by removing G\H from the original G, never by calling pinnedSum with volume H. -/
def componentSum (G H : Finset Plane) (τ : PinAssignment G) : ℝ :=
  pinnedSum G (G \ H) τ (fun _ => 1)

def windowWeight (κ : Plane → Fin 3) (B : Finset Plane) (s : PlaneConfiguration B) : ℝ :=
  (1 / 12 : ℝ) ^ B.card * ∏ e ∈ internalBonds B,
    (1 + dot (frameVector (κ e.1) (extendLetters s e.1))
      (frameVector (κ e.2) (extendLetters s e.2)))

def cutError (G X : Finset Plane) (τ : PinAssignment G) : ℝ :=
  logRatio G X τ - logRatio G ∅ τ

def coord (axis : Fin 2) (z : Plane) : ℤ := if axis = 0 then z.1 else z.2

def SignedUnit (ε : ℤ) : Prop := ε = 1 ∨ ε = -1

def NoCoincidence (a y : Plane) (u : ℕ) (i : ℤ) : Prop :=
  ∀ j : ℕ, (j : ℝ) ≤ shellSpacing u / 12 →
  ∀ h : ℤ, 30 + (j : ℤ) ≤ h → h < 32 + (j : ℤ) →
  ∀ r : ℤ, (r = shellRadius u i - j ∨ r = shellRadius u i + j) →
  ∀ axis : Fin 2, ∀ ε δ : ℤ, SignedUnit ε → SignedUnit δ →
    coord axis y + ε * r ≠ coord axis a + δ * ((u : ℤ) + 1 - h)

def sphere (a : Plane) (r : ℤ) : Finset Plane := by
  classical
  exact (square a r.toNat).filter fun z => (supDist z a : ℤ) = r

def tailCost (θ : ℝ) (u : ℕ) : ℝ :=
  4 * (2 * (u : ℝ) + 1) ^ 2 * θ ^ (shellSpacing u / 12 - 1)

def tailConstant (θ : ℝ) : ℝ :=
  36 * θ⁻¹ * (Nat.factorial 10 : ℝ) * (12 / (-Real.log θ)) ^ 10

structure RemovalEnumeration (X : Finset Plane) where
  last : ℕ
  site : Fin (last + 1) → Plane
  injective : Function.Injective site
  image_eq : Finset.univ.image site = X
  previous : ∀ j : Fin (last + 1), 0 < j.val →
    ∃ k : Fin (last + 1), k.val < j.val ∧ Adjacent (site j) (site k)

def removedPrefix {X : Finset Plane} (e : RemovalEnumeration X) (j : ℕ) : Finset Plane := by
  classical
  exact (Finset.univ.filter fun k : Fin (e.last + 1) => k.val < j).image e.site

def RemovalStep (G Y : Finset Plane) (x : Plane) : Prop :=
  Y ⊆ G \ protectedSites G ∧ x ∈ G \ Y ∧ 3 ≤ boundaryDepth G x

def survivors (G Y : Finset Plane) (x : Plane) : Finset Plane :=
  neighbours x ∩ (G \ insert x Y)

def depthShift (G : Finset Plane) (x : Plane) : ℕ := (boundaryDepth G x).toNat - 3

def partWeight (pinned : Bool) (G Y : Finset Plane) (τ : PinAssignment G)
    (σ : PlaneConfiguration (G \ Y)) : ℝ :=
  (1 / 12 : ℝ) ^ (G \ Y).card *
  (∏ e ∈ internalBonds (G \ Y),
    (1 + dot (extendIcoSpins σ e.1) (extendIcoSpins σ e.2))) *
  ∏ e : originalLegs G,
    if pinned ∧ e.val.1 ∈ G \ Y then
      1 + dot (τ e).val (extendIcoSpins σ e.val.1) else 1

def partLaw (pinned : Bool) (G Y : Finset Plane) (τ : PinAssignment G) :
    Weight (PlaneConfiguration (G \ Y)) := normalize (partWeight pinned G Y τ)

def restEvent {D : Finset Plane} (V : Finset Plane) (σ ω : PlaneConfiguration D) : Prop :=
  ∀ z : D, z.val ∉ V → ω z = σ z

def fibreMean {D : Finset Plane} (p : Weight (PlaneConfiguration D)) (V : Finset Plane)
    (σ : PlaneConfiguration D) (f : PlaneConfiguration D → ℝ) : ℝ := by
  classical
  exact (∑ ω, if restEvent V σ ω then p ω * f ω else 0) / eventMass p (restEvent V σ)

def fibreSpinMean {D : Finset Plane} (p : Weight (PlaneConfiguration D)) (V : Finset Plane)
    (σ : PlaneConfiguration D) (z : Plane) : Vec3 :=
  fun k => fibreMean p V σ (fun ω => extendIcoSpins ω z k)

def NeighbourControl {D : Finset Plane} (p : Weight (PlaneConfiguration D))
    (V : Finset Plane) : Prop :=
  ∀ σ : PlaneConfiguration D, 0 < eventMass p (restEvent V σ) →
    (∀ z ∈ V, normSq (fibreSpinMean p V σ z) ≤ (3 / 5 : ℝ)^2) ∧
    ∀ z ∈ V, ∀ w ∈ V, z ≠ w →
      fibreMean p V σ (fun ω => dot (extendIcoSpins ω z) (extendIcoSpins ω w)) =
        dot (fibreSpinMean p V σ z) (fibreSpinMean p V σ w)

def frameSpins {D : Finset Plane} (κ : Plane → Fin 3)
    (σ : PlaneConfiguration D) (z : Plane) : Vec3 :=
  if h : z ∈ D then frameVector (κ z) (σ ⟨z, h⟩) else 0

def framePinnedSum (κ : Plane → Fin 3) (G Y : Finset Plane) (τ : PinAssignment G) : ℝ :=
  ∑ σ : PlaneConfiguration (G \ Y), (1 / 12 : ℝ) ^ (G \ Y).card *
    (∏ e ∈ internalBonds (G \ Y),
      (1 + dot (frameSpins κ σ e.1) (frameSpins κ σ e.2))) *
    ∏ e : originalLegs G,
      if e.val.1 ∈ G \ Y then 1 + dot (τ e).val (frameSpins κ σ e.val.1) else 1

def marginalNumerator (κ : Plane → Fin 3) (F B : Finset Plane)
    (η : FrameBoundary F) (s : PlaneConfiguration B) : ℝ := by
  classical
  exact ∑ σ : PlaneConfiguration F,
    if (fun z : B => extendLetters σ z.val) = s then planeWeight κ F η σ else 0

abbrev LatticeEdge := Sym2 Plane
abbrev EdgeChain := LatticeEdge →₀ ZMod 2

def edge (x y : Plane) : EdgeChain := Finsupp.single s(x, y) 1

def triangle (x y z : Plane) : EdgeChain := edge x y + edge y z + edge z x

def IsTriangle (x y z : Plane) : Prop :=
  StarAdjacent x y ∧ StarAdjacent y z ∧ StarAdjacent z x

def triangleSpan : Submodule (ZMod 2) EdgeChain :=
  Submodule.span (ZMod 2) {c | ∃ x y z, IsTriangle x y z ∧ c = triangle x y z}

def ChainStar (c : EdgeChain) : Prop :=
  ∀ e ∈ c.support, ∃ x y, e = s(x, y) ∧ StarAdjacent x y

def ChainNN (c : EdgeChain) : Prop :=
  ∀ e ∈ c.support, ∃ x y, e = s(x, y) ∧ Adjacent x y

def ChainEven (c : EdgeChain) : Prop :=
  ∀ x : Plane, (∑ e ∈ c.support, if x ∈ e then c e else 0) = 0

def ChainInBox (c : EdgeChain) (R : ℤ) : Prop :=
  ∀ e ∈ c.support, ∀ x ∈ e, |x.1| ≤ R ∧ |x.2| ≤ R

def horizontal (c : EdgeChain) (i j : ℤ) : ZMod 2 := c s((i, j), (i + 1, j))

def tailCoefficient (c : EdgeChain) (R i j : ℤ) : ZMod 2 :=
  ∑ r ∈ Finset.Icc (-R) R, if j < r then horizontal c i r else 0

def plaquette (p : Plane) : EdgeChain :=
  edge p (p + (1, 0)) + edge (p + (1, 0)) (p + (1, 1)) +
  edge (p + (1, 1)) (p + (0, 1)) + edge (p + (0, 1)) p

def cutEdges (A : Finset Plane) : Finset LatticeEdge :=
  A.biUnion fun x => ((starBall x) \ A).image fun y => s(x, y)

def Linked (e f : LatticeEdge) : Prop :=
  ∃ x y z, IsTriangle x y z ∧
    e ∈ ({s(x, y), s(y, z), s(z, x)} : Finset LatticeEdge) ∧
    f ∈ ({s(x, y), s(y, z), s(z, x)} : Finset LatticeEdge)

def LinkClosed (A : Finset Plane) (E : Finset LatticeEdge) : Prop :=
  E ⊆ cutEdges A ∧ ∀ e ∈ E, ∀ f ∈ cutEdges A, Linked e f → f ∈ E

def cutParity (E : Finset LatticeEdge) (c : EdgeChain) : ZMod 2 := ∑ e ∈ E, c e

def TwoCrossings (A : Finset Plane) (e f : LatticeEdge) (c : EdgeChain) : Prop :=
  ∀ g ∈ cutEdges A, c g = if g = e ∨ g = f then 1 else 0

end AKLT.Blueprint.Win
