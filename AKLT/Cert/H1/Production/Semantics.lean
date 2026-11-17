module
public import AKLT.Cert.H1.Production.Input
public import AKLT.Cert.H1.Contraction
public import AKLT.Blueprint.Top.Operator

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

/-! Semantic interfaces contain definitions only. Generated computation modules
depend on Basic/Input; only the small bridge modules import this file. -/
namespace AKLT.Cert.H1.Production
open AKLT.Defs AKLT.Gen.Gram
open scoped BigOperators ComplexOrder
noncomputable section

def groupPoint (i : Nat) : Plane :=
  let x := ringSites.getD i (0,0)
  if i%2 == 0 then (2*x.1,2*x.2) else x

def groupSlots (π : PatternData) (r : Representation) (x : Plane) : Nat :=
  if x ∈ reductionGroups π then if groupIsPair π r x then 2 else 1 else 0

def groupDim (π : PatternData) (r : Representation) (x : Plane) : Nat :=
  if groupSlots π r x == 0 then 1 else if groupSlots π r x == 1 then 2
  else if π.statusAt x = .D then 4 else 3

def NetworkGeometry (π : PatternData) (r : Representation) (I : Finset (Fin 20))
    (ss : List PackedSite) : Prop :=
  ss.length = 8 ∧ ∀ si ∈ ss.zipIdx,
    let s := si.1
    let i := si.2
    let x := ringSites.getD i (0,0)
    let gx := groupPoint i
    s.spec.left = presentBond π (ringSites.getD ((i+7)%8) (0,0)) x ∧
    s.spec.right = presentBond π x (ringSites.getD ((i+1)%8) (0,0)) ∧
    s.spec.center = presentBond π x (0,0) ∧
    s.spec.nslots = groupSlots π r gx ∧ s.spec.dim = groupDim π r gx ∧
    s.spec.diluted = decide (π.statusAt x = .D) ∧
    s.spec.leaf = (by classical exact decide (i%2 = 1 ∧ SingleReplacement π r x)) ∧
    s.spec.tip = decide (i%2 = 0 ∧ gx ∈ reductionGroups π) ∧
    s.spec.inverted = decide (groupLeader gx ∈ I) ∧
    s.spec.stride = ((ss.drop (i+1)).map (fun t => t.spec.dim)).prod ∧
    tableCheck s.spec s.table = true

def exchangeBasisCode (π : PatternData) (r : Representation) (ε : ExchangeSigns π)
    (b : ExchangeBasis π r ε) : Nat :=
  (List.range 8).foldl (fun code i =>
    let x := groupPoint i
    let digit := if h : x ∈ reductionGroups π then
      if groupIsPair π r x && decide (π.statusAt x = .D ∧ ε ⟨x,h⟩ = false) then 3
      else (b ⟨x,h⟩).val else 0
    code * groupDim π r x + digit) 0

def exchangeParity (π : PatternData) (r : Representation) (ε : ExchangeSigns π) : Nat :=
  (List.range 8).foldl (fun par i =>
    let x := groupPoint i
    if h : x ∈ reductionGroups π then
      2*par + (if groupIsPair π r x && decide (π.statusAt x = .D ∧ ε ⟨x,h⟩ = false)
        then 1 else 0) else par) 0

def directSiteMatrix (s : PackedSite) (row col v : Nat) : FourMatrix :=
  let a := row / s.spec.stride % s.spec.dim
  let b := col / s.spec.stride % s.spec.dim
  (List.range 4).map fun l => (List.range 4).map fun r =>
    s.table.get (tableIndex s.spec.dim a l r v b)

def directRingProduct (row col : Nat) : List PackedSite → List Nat → FourMatrix
  | [], _ => fourIdentity
  | s :: ss, codes => fourMul (directSiteMatrix s row col (codes.headD 0))
      (directRingProduct row col ss codes.tail)

def directRingValue (ss : List PackedSite) (row col : Nat) (codes : List Nat) : Gaussian :=
  fourTrace (directRingProduct row col ss codes)

def directCurrentNext (ss : List PackedSite) (out row col : Nat) (next : Bool) : Gaussian :=
  let Z := directRingValue ss row col []
  let terms := (centerPairs ss).filterMap fun (x,y) =>
    if next && (x == out || y == out) then none else
      some (sumGaussian ((List.range 3).map fun k =>
        directRingValue ss row col (centerCodes ss.length x y (k+1))))
  (Z.scale (if next then 5 else 3)).add (sumGaussian terms)

def directSectorSiteMatrix (s : SectorSite) (row col v : Nat) : FourMatrix :=
  let a := s.coordinates.getD (row / s.stride % s.coordinates.length) 0
  let b := s.coordinates.getD (col / s.stride % s.coordinates.length) 0
  (List.range 4).map fun l => (List.range 4).map fun r =>
    s.base.table.get (tableIndex s.base.spec.dim a l r v b)

def directSectorRingProduct (row col : Nat) : List SectorSite → List Nat → FourMatrix
  | [], _ => fourIdentity
  | s :: ss, codes => fourMul (directSectorSiteMatrix s row col (codes.headD 0))
      (directSectorRingProduct row col ss codes.tail)

def directSectorRingValue (ss : List SectorSite) (row col : Nat) (codes : List Nat) : Gaussian :=
  fourTrace (directSectorRingProduct row col ss codes)

def directSectorCurrentNext (ss : List SectorSite) (out row col : Nat) (next : Bool) : Gaussian :=
  let Z := directSectorRingValue ss row col []
  let terms := (centerPairs (ss.map (fun s => s.base))).filterMap fun (x,y) =>
    if next && (x == out || y == out) then none else
      some (sumGaussian ((List.range 3).map fun k =>
        directSectorRingValue ss row col (centerCodes ss.length x y (k+1))))
  (Z.scale (if next then 5 else 3)).add (sumGaussian terms)

def directSectorThreshold (ss : List SectorSite) (out p q row col : Nat) : Gaussian :=
  ((directSectorCurrentNext ss out row col false).scale (5*q)).add
    ((directSectorCurrentNext ss out row col true).scale (-(3*(p : Int))))

def directSectorRows (ss : List SectorSite) (out p q : Nat) (indices : List Nat) : IntRows :=
  indices.map (fun row => indices.map (fun col => (directSectorThreshold ss out p q row col).re))

def TablesAccepted : List PackedSite → Prop
  | [] => True
  | s :: ss => tableCheck s.spec s.table = true ∧ TablesAccepted ss

structure Bundle where
  block : Block
  sector : List SectorSite
  mapped : List Nat

structure Case where
  input : Input
  network : List PackedSite
  out : Nat
  width : Nat
  lanes : Nat
  denominator : Nat
  p : Nat
  q : Nat
  bundles : List Bundle

def Case.MetadataAccepted (c : Case) : Prop :=
  inputCheck c.input = true ∧ geometryCheck c.input c.network = true ∧
  TablesAccepted c.network ∧
  parametersCheck c.network c.out c.width c.lanes c.denominator c.p c.q = true ∧
  c.out = 2*c.input.outgoing ∧
  c.p = h1Numerator (inputPattern c.input) ∧ c.q = h1Denominator (inputPattern c.input) ∧
  parityCoverCheck c.network (c.bundles.map (fun b => b.block.parity)) = true

def Bundle.LayoutAccepted (c : Case) (b : Bundle) : Prop :=
  basisCheck c.network b.block.parity b.block.weight b.block.indices = true ∧
  sectorNetworkCheck c.network b.block.parity b.sector = true ∧
  remapCheck c.network b.sector b.block.indices b.mapped = true ∧
  b.block.indices.length = b.block.M.length ∧ b.mapped.length = b.block.M.length

def Bundle.Accepted (c : Case) (b : Bundle) : Prop :=
  b.LayoutAccepted c ∧
  SectorRowsAccepted b.sector c.out c.width c.p c.q b.mapped b.mapped b.block.M ∧
  b.block.Accepted

def BundlesAccepted (c : Case) : List Bundle → Prop
  | [] => True
  | b :: bs => b.Accepted c ∧ BundlesAccepted c bs

def Case.Accepted (c : Case) : Prop := c.MetadataAccepted ∧ BundlesAccepted c c.bundles

def Bundle.Indexed (c : Case) (b : Bundle) (ε : ExchangeSigns (inputPattern c.input)) : Prop :=
  ∃ index : Fin b.block.M.length ≃ CentralBasis (inputPattern c.input) (inputRepresentation c.input) ε,
    ∀ i : Fin b.block.M.length,
      b.block.indices.getD i 0 =
        exchangeBasisCode (inputPattern c.input) (inputRepresentation c.input) ε (index i).val

def RawWitness (π : PatternData) : Prop :=
  ∃ r : Representation, ∃ I : Finset (Fin 20), GroupInversion π r I ∧
    ∃ D₀ : Nat, ClearsDenominator π r D₀ ∧ H1SectorWitnesses π r I D₀ (h1Numerator π) (h1Denominator π)

def SameEffectiveData (π ρ : PatternData) : Prop :=
  π.outgoing = ρ.outgoing ∧ π.bonds = ρ.bonds ∧
    ∀ x : Plane, 0 < patternDegree π x → π.statusAt x = ρ.statusAt x

def MirrorEffectiveData (π ρ : PatternData) : Prop :=
  π.outgoing.step = reflectPoint true ρ.outgoing.step ∧
    (∀ a b : Plane, presentBond π a b = presentBond ρ (reflectPoint true a) (reflectPoint true b)) ∧
    ∀ x : Plane, 0 < patternDegree π x → π.statusAt x = ρ.statusAt (reflectPoint true x)

structure Representative where
  pid : Nat
  input : Input

def Representative.key (r : Representative) : Nat := rawKey r.input.axes r.input.corners r.input.outgoing

def representativeCheck (t : Catalog) (rs : List Representative) : Bool :=
  t.entries == rs.map (fun r => (r.key,r.pid))

def RepresentativesAccepted : List Representative → Prop
  | [] => True
  | r :: rs => inputCheck r.input = true ∧ (inputPattern r.input).Covered ∧
      RawWitness (inputPattern r.input) ∧ RepresentativesAccepted rs

end
end AKLT.Cert.H1.Production
