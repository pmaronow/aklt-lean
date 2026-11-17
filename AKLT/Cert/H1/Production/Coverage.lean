module
public import AKLT.Cert.H1.Production.Basic

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

/-! Finite raw enumeration, local consistency pruning and balanced catalog
lookup. Every loop is structural on lists/Nat; no trusted native computation. -/
namespace AKLT.Cert.H1.Production

structure RawOption where
  status : Nat
  mask : Nat
  deriving BEq, DecidableEq, Repr

def hasDirection (mask direction : Nat) : Bool := mask / 2^direction % 2 == 1

def cornerOptions : List RawOption :=
  [⟨1,15⟩,⟨0,0⟩,⟨2,3⟩,⟨2,5⟩,⟨2,9⟩,⟨2,6⟩,⟨2,10⟩,⟨2,12⟩]

def axialOptions (i : Nat) : List RawOption :=
  if i == 3 then [⟨0,0⟩,⟨2,5⟩,⟨2,9⟩,⟨2,12⟩]
  else [⟨1,15⟩,⟨0,0⟩] ++
    ((List.range 4).filter (fun d => d != (i+2)%4)).map
      (fun d => ⟨2,2^((i+2)%4)+2^d⟩)

def axialConfigurations : List (List RawOption) :=
  (axialOptions 0).flatMap fun e => (axialOptions 1).flatMap fun n =>
    (axialOptions 2).flatMap fun w => (axialOptions 3).map fun s => [e,n,w,s]

/-- Each pair records an adjacent axial index and direction from this corner. -/
def cornerAdjacency (i : Nat) : List (Nat × Nat) :=
  if i == 0 then [(0,3),(1,2)] else if i == 1 then [(1,0),(2,3)]
  else if i == 2 then [(2,1),(3,0)] else [(3,2),(0,1)]

def cornerCompatible (axes : List RawOption) (i : Nat) (c : RawOption) : Bool :=
  (cornerAdjacency i).all fun (ai,d) =>
    let a := axes.getD ai ⟨0,0⟩
    c.status == 0 || a.status == 0 ||
      (hasDirection c.mask d == hasDirection a.mask ((d+2)%4))

def allowedCorners (axes : List RawOption) (i : Nat) : List RawOption :=
  cornerOptions.filter (cornerCompatible axes i)

def ringOptions (axes corners : List RawOption) : List RawOption :=
  (List.range 8).map fun i =>
    if i%2 == 0 then axes.getD (i/2) ⟨0,0⟩ else corners.getD (i/2) ⟨0,0⟩

def edgeDirections : List Nat := [1,2,2,3,3,0,0,1]

def rawEdges (axes corners : List RawOption) : List Bool :=
  let ring := ringOptions axes corners
  let center := (List.range 4).map fun i =>
    let a := axes.getD i ⟨0,0⟩
    i != 3 && a.status != 0 && hasDirection a.mask ((i+2)%4)
  let cycle := (List.range 8).map fun i =>
    let a := ring.getD i ⟨0,0⟩
    let b := ring.getD ((i+1)%8) ⟨0,0⟩
    let d := edgeDirections.getD i 0
    a.status != 0 && b.status != 0 && hasDirection a.mask d && hasDirection b.mask ((d+2)%4)
  let tips := (List.range 4).map fun i =>
    let a := axes.getD i ⟨0,0⟩
    a.status != 0 && hasDirection a.mask i
  center ++ cycle ++ tips

def rawStatusDigits (axes corners : List RawOption) (edges : List Bool) : List Nat :=
  ((ringOptions axes corners).zipIdx).map fun (s,i) =>
    let live := edges.getD (4+i) false || edges.getD (4+(i+7)%8) false ||
      (i%2 == 0 && (edges.getD (i/2) false || edges.getD (12+i/2) false))
    if live then s.status else 0

def reflectSites : List Nat := [4,3,2,1,0,7,6,5]
def reflectEdges : List Nat := [2,1,0,3,7,6,5,4,11,10,9,8,14,13,12,15]

def rawCode (axes corners : List RawOption) (out : Nat) (reflect : Bool) : Nat :=
  let edges := rawEdges axes corners
  let status := rawStatusDigits axes corners edges
  let sd := if reflect then reflectSites.map (fun i => status.getD i 0) else status
  let ed := if reflect then reflectEdges.map (fun i => edges.getD i false) else edges
  let o := if reflect then if out == 0 then 2 else if out == 2 then 0 else out else out
  (encodeDigits 3 sd * 65536 + encodeDigits 2 (ed.map Bool.toNat))*3+o

def rawKey (axes corners : List RawOption) (out : Nat) : Nat :=
  min (rawCode axes corners out false) (rawCode axes corners out true)

inductive Catalogue where
  | empty
  | node (key pid : Nat) (left right : Catalogue)
  deriving BEq, DecidableEq

def Catalogue.find : Catalogue → Nat → Option Nat
  | .empty, _ => none
  | .node key pid l r, x =>
    if x == key then some pid else if x < key then l.find x else r.find x

def Catalogue.entries : Catalogue → List (Nat × Nat)
  | .empty => []
  | .node key pid l r => l.entries ++ [(key,pid)] ++ r.entries

def catalogueCheck (t : Catalogue) (codes pids : List Nat) : Bool :=
  (t.entries == codes.zip pids) && strictlyIncreasing codes &&
    (codes.length == 7962) && (pids.length == 7962)

def markedCheck (t : Catalogue) (axes corners : List RawOption) : Bool :=
  let edges := rawEdges axes corners
  let status := rawStatusDigits axes corners edges
  let plain := encodeDigits 3 status * 65536 + encodeDigits 2 (edges.map Bool.toNat)
  let reflected := encodeDigits 3 (reflectSites.map (fun i => status.getD i 0)) * 65536 +
    encodeDigits 2 ((reflectEdges.map (fun i => edges.getD i false)).map Bool.toNat)
  (List.range 3).all fun out =>
    !(edges.getD out false) || (t.find (min (plain*3+out)
      (reflected*3+(if out == 0 then 2 else if out == 2 then 0 else out)))).isSome

/-- The first corner is fixed, leaving only locally consistent choices of the
other three. Invalid first choices contribute true, and have no raw completion. -/
def coverageShard (t : Catalogue) (axes : List RawOption) (first : Nat) : Bool :=
  let c0 := cornerOptions.getD first ⟨0,0⟩
  if (axes.take 3).all (fun a => a.status == 0) then true
  else if cornerCompatible axes 0 c0 then
    (allowedCorners axes 1).all fun c1 => (allowedCorners axes 2).all fun c2 =>
      (allowedCorners axes 3).all fun c3 => markedCheck t axes [c0,c1,c2,c3]
  else true

/-- A replay frontier explicitly lists the eight first-corner obligations. -/
def CoverageAccepted (t : Catalogue) (axes : List RawOption) : Prop :=
  coverageShard t axes 0 = true ∧ coverageShard t axes 1 = true ∧
  coverageShard t axes 2 = true ∧ coverageShard t axes 3 = true ∧
  coverageShard t axes 4 = true ∧ coverageShard t axes 5 = true ∧
  coverageShard t axes 6 = true ∧ coverageShard t axes 7 = true

def FullCoverageAccepted (t : Catalogue) : Prop :=
  ∀ axes ∈ axialConfigurations, CoverageAccepted t axes

def CoverageRowsAccepted (t : Catalogue) : List (List RawOption) → Prop
  | [] => True
  | axes :: rest => CoverageAccepted t axes ∧ CoverageRowsAccepted t rest

end AKLT.Cert.H1.Production
