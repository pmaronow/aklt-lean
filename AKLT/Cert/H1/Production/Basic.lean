module
public import AKLT.Cert.H1.PackedConstructor
public import AKLT.Cert.H1.Soundness
public import AKLT.Cert.H1.Coverage

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

/-! Executable production checks. Soundness is stated in Production.Leaves;
this file deliberately contains no proof of a mathematical leaf. -/
namespace AKLT.Cert.H1.Production
open AKLT.Gen.Gram

def sparsePack (width : Nat) : List Nat → List Int → Int
  | i :: is, a :: as => a * ((2 : Nat) ^ (width*i) : Int) + sparsePack width is as
  | _, _ => 0

/-- Checks the imaginary part and the complete packed row, including all
columns outside the selected weight/parity block. -/
def packedRowCheck (ss : List PackedSite) (out width p q row : Nat)
    (indices : List Nat) (expected : List Int) : Bool :=
  (indices.length == expected.length) &&
  (expected.all fun a => decide (-((2 : Nat)^(width-1) : Int) ≤ a ∧
    a < ((2 : Nat)^(width-1) : Int))) &&
  (packedThresholdRow ss out row width p q == ⟨sparsePack width indices expected, 0⟩)

/-- A conjunction assembled from independent kernel reductions, never one
large reduction retaining the work of every row. -/
def RowsAccepted (ss : List PackedSite) (out width p q : Nat) (columns : List Nat) :
    List Nat → IntRows → Prop
  | [], [] => True
  | i :: is, row :: rows => packedRowCheck ss out width p q i columns row = true ∧
      RowsAccepted ss out width p q columns is rows
  | _, _ => False

def tableAbs : Table → Nat
  | .empty => 0
  | .leaf z => z.re.natAbs + z.im.natAbs
  | .node _ l r => tableAbs l + tableAbs r

def tableShape (span : Nat) : Table → Bool
  | .empty => true
  | .leaf _ => span == 1
  | .node cut l r => (cut == span / 2) && (0 < cut) && (cut < span) &&
      tableShape cut l && tableShape (span-cut) r

def bound (ss : List PackedSite) (p q : Nat) : Nat :=
  (ss.map (fun s => tableAbs s.table)).prod * (5*q*12+3*p*8)

def parametersCheck (ss : List PackedSite) (out width lanes denominator p q : Nat) : Bool :=
  (ss.length == 8) && (out == 0 || out == 2) && (0 < width) && (0 < p) && (p < q) &&
  ((ss.map (fun s => s.spec.dim)).prod == lanes) &&
  ((ss.map (fun s => s.spec.totalDen)).prod == denominator) &&
  (bound ss p q < 2^(width-1)) &&
  (ss.zipIdx.all fun (s,i) =>
    (0 < s.spec.dim) && (s.spec.nslots ≤ 2) &&
    (s.spec.dim == if s.spec.nslots == 0 then 1 else if s.spec.nslots == 1 then 2
      else if s.spec.diluted then 4 else 3) &&
    (s.spec.stride == ((ss.drop (i+1)).map (fun t => t.spec.dim)).prod) &&
    tableShape (s.spec.dim * 64 * s.spec.dim) s.table)

def localWeight (s : SiteSpec) (digit : Nat) : Int :=
  if s.nslots == 0 then 0 else if s.nslots == 1 then 1 - 2*(digit : Int)
  else if digit == 3 then 0 else 2 - 2*(digit : Int)

def sectorLabel (ss : List PackedSite) (index : Nat) : Nat × Int :=
  ss.foldl (fun (par,sz) s =>
    let digit := index / s.spec.stride % s.spec.dim
    (if s.spec.nslots == 0 then par else
       2*par + (if s.spec.nslots == 2 && s.spec.diluted && digit == 3 then 1 else 0),
     sz + localWeight s.spec digit)) (0,0)

def exchangeParities : List PackedSite → List Nat
  | [] => [0]
  | s :: ss =>
    let tails := exchangeParities ss
    let groups := ((ss.filter (fun t => t.spec.nslots != 0)).length)
    if s.spec.nslots == 0 then tails
    else if s.spec.nslots == 2 && s.spec.diluted then
      tails ++ tails.map (fun p => 2^groups+p)
    else tails

def centralWeight (ss : List PackedSite) : Int :=
  if (ss.filter (fun s => s.spec.nslots == 1)).length % 2 == 0 then 0 else 1

def sectorIndices (ss : List PackedSite) (parity : Nat) (weight : Int) : List Nat :=
  (List.range ((ss.map (fun s => s.spec.dim)).prod)).filter fun i =>
    sectorLabel ss i == (parity,weight)

def basisCheck (ss : List PackedSite) (parity : Nat) (weight : Int) (indices : List Nat) : Bool :=
  (weight == centralWeight ss) && (exchangeParities ss).contains parity &&
    (indices == sectorIndices ss parity weight) && (!indices.isEmpty)

def parityCoverCheck (ss : List PackedSite) (parities : List Nat) : Bool :=
  parities == exchangeParities ss

structure Block where
  M : IntRows
  L : IntRows
  g : Nat
  d : Nat
  S : Nat
  parity : Nat
  weight : Int
  indices : List Nat

def Block.Accepted (b : Block) : Prop :=
  checker b.M b.L b.g b.d b.S = true ∧ lowerTriangularCheck b.L = true

/-- Parity is split before packing: a D symmetric pair has coordinates
0,1,2, and a D exterior pair has the single coordinate 3. -/
structure SectorSite where
  base : PackedSite
  coordinates : List Nat
  stride : Nat

def sectorSiteMatrix (s : SectorSite) (row v width : Nat) : FourMatrix :=
  let a := s.coordinates.getD (row / s.stride % s.coordinates.length) 0
  let base : Int := (2 : Nat) ^ (width*s.stride)
  (List.range 4).map fun l => (List.range 4).map fun r =>
    packGaussian base (s.coordinates.map fun b =>
      s.base.table.get (tableIndex s.base.spec.dim a l r v b))

def sectorRingProduct (row width : Nat) : List SectorSite → List Nat → FourMatrix
  | [], _ => fourIdentity
  | s :: ss, codes => fourMul (sectorSiteMatrix s row (codes.headD 0) width)
      (sectorRingProduct row width ss codes.tail)

def sectorRingValue (ss : List SectorSite) (row width : Nat) (codes : List Nat) : Gaussian :=
  fourTrace (sectorRingProduct row width ss codes)

def packedSectorThresholdRow (ss : List SectorSite) (out row width p q : Nat) : Gaussian :=
  let Z := sectorRingValue ss row width []
  let terms := (centerPairs (ss.map (fun s => s.base))).map fun (x,y) =>
    (x,y,sumGaussian ((List.range 3).map fun k =>
      sectorRingValue ss row width (centerCodes ss.length x y (k+1))))
  let cur := (Z.scale 3).add (sumGaussian (terms.map fun (_,_,c) => c))
  let nxt := (Z.scale 5).add (sumGaussian (terms.filterMap fun (x,y,c) =>
    if x != out && y != out then some c else none))
  (cur.scale (5*q)).add (nxt.scale (-(3*(p : Int))))

def packedSectorRowCheck (ss : List SectorSite) (out width p q row : Nat)
    (indices : List Nat) (expected : List Int) : Bool :=
  (indices.length == expected.length) &&
  (expected.all fun a => decide (-((2 : Nat)^(width-1) : Int) ≤ a ∧
    a < ((2 : Nat)^(width-1) : Int))) &&
  (packedSectorThresholdRow ss out row width p q == ⟨sparsePack width indices expected, 0⟩)

def SectorRowsAccepted (ss : List SectorSite) (out width p q : Nat) (columns : List Nat) :
    List Nat → IntRows → Prop
  | [], [] => True
  | i :: is, row :: rows => packedSectorRowCheck ss out width p q i columns row = true ∧
      SectorRowsAccepted ss out width p q columns is rows
  | _, _ => False

def sectorCoordinates (s : SiteSpec) (bit : Nat) : List Nat :=
  if s.nslots == 2 && s.diluted then
    if bit == 1 then [3] else [0,1,2]
  else List.range s.dim

def sectorNetworkCheck (base : List PackedSite) (parity : Nat) (ss : List SectorSite) : Bool :=
  (ss.length == base.length) && ((base.zip ss).zipIdx.all fun ((b,s),i) =>
    let following := ((base.drop (i+1)).filter (fun t => t.spec.nslots != 0)).length
    (s.base.spec == b.spec) && (s.base.table == b.table) &&
    (s.coordinates == sectorCoordinates b.spec (parity / 2^following % 2)) &&
    (s.stride == ((ss.drop (i+1)).map (fun t => t.coordinates.length)).prod))

def remapIndex (base : List PackedSite) (ss : List SectorSite) (index : Nat) : Nat :=
  (base.zip ss).foldl (fun code (b,s) =>
    let digit := index / b.spec.stride % b.spec.dim
    code*s.coordinates.length + (s.coordinates.idxOf digit)) 0

def remapCheck (base : List PackedSite) (ss : List SectorSite)
    (indices mapped : List Nat) : Bool :=
  (indices.map (remapIndex base ss)) == mapped

def constructedSectorRow (ss : List SectorSite) (out width lanes p q row : Nat)
    (indices : List Nat) : List Int :=
  let packed := (packedSectorThresholdRow ss out row width p q).re + signedBias width lanes
  indices.map (fun j => signedDigit packed width j)

def constructedSectorRows (ss : List SectorSite) (out width lanes p q : Nat)
    (indices : List Nat) : IntRows :=
  indices.map (fun i => constructedSectorRow ss out width lanes p q i indices)

end AKLT.Cert.H1.Production
