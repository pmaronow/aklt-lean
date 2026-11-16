import AKLT.Cert.H1.Production.Coverage

namespace AKLT.Cert.H1.Production
open AKLT.Defs

structure Input where
  axes : List RawOption
  corners : List RawOption
  outgoing : Nat
  leafReduced : Bool
  inversion : List Nat

def Input.optionAt (a : Input) (x : Plane) : RawOption :=
  ((ringSites.zip (ringOptions a.axes a.corners)).find? (fun p => p.1 == x)).map
    Prod.snd |>.getD ⟨0,0⟩

def compassAt (i : Nat) : Compass :=
  if i == 0 then .east else if i == 1 then .north else if i == 2 then .west else .south

def inputPattern (a : Input) : PatternData where
  outgoing := compassAt a.outgoing
  status := fun x =>
    if x.val == (0,0) || ([(2,0),(0,2),(-2,0),(0,-2)] : List Plane).contains x.val then .U
    else if (a.optionAt x.val).status == 1 then .U
    else if (a.optionAt x.val).status == 2 then .D else .X
  kept := fun x =>
    if x.val == (0,0) then {.east,.north,.west}
    else ((List.range 4).filter (fun d => hasDirection (a.optionAt x.val).mask d)).map
      compassAt |>.toFinset

def inputRepresentation (a : Input) : Representation :=
  if a.leafReduced then .reduced else .unreduced

def inputInversion (a : Input) : Finset (Fin 20) :=
  (a.inversion.filterMap (fun i => if h : i < 20 then some ⟨i,h⟩ else none)).toFinset

def ringLeader (i : Nat) : Nat := [8,0,11,2,14,4,17,6].getD i 0

def inputSlots (a : Input) (i : Nat) : Nat :=
  let es := rawEdges a.axes a.corners
  if i%2 == 0 then if es.getD (12+i/2) false then 1 else 0
  else
    let degree := (es.getD (4+i) false).toNat + (es.getD (4+(i+7)%8) false).toNat
    if degree == 0 then 0 else if a.leafReduced && degree == 1 then 1 else 2

def inputDimension (a : Input) (i : Nat) : Nat :=
  let n := inputSlots a i
  if n == 0 then 1 else if n == 1 then 2
  else if ((ringOptions a.axes a.corners).getD i ⟨0,0⟩).status == 2 then 4 else 3

def inputTokens (a : Input) : List Nat :=
  (List.range 8).flatMap (fun i => (List.range (inputSlots a i)).map (ringLeader i + ·))

def inputCheck (a : Input) : Bool :=
  (a.axes.length == 4) && (a.corners.length == 4) && (a.outgoing < 3) &&
  ((a.axes.zipIdx).all fun (x,i) => (axialOptions i).contains x) &&
  ((a.corners.zipIdx).all fun (x,i) => cornerOptions.contains x && cornerCompatible a.axes i x) &&
  (rawEdges a.axes a.corners).getD a.outgoing false &&
  strictlyIncreasing a.inversion && (a.inversion.all fun i => (inputTokens a).contains i) &&
  ((List.range 8).all fun i => inputSlots a i != 2 ||
    (a.inversion.contains (ringLeader i) == a.inversion.contains (ringLeader i+1)))

def inputSpec (a : Input) (i : Nat) : SiteSpec :=
  let es := rawEdges a.axes a.corners
  let slots := inputSlots a i
  ⟨inputDimension a i, es.getD (4+(i+7)%8) false, es.getD (4+i) false,
    i%2 == 0 && es.getD (i/2) false, slots,
    ((ringOptions a.axes a.corners).getD i ⟨0,0⟩).status == 2,
    i%2 == 1 && slots == 1, i%2 == 0 && slots == 1,
    a.inversion.contains (ringLeader i),
    (((List.range 8).drop (i+1)).map (inputDimension a)).prod⟩

def geometryCheck (a : Input) (ss : List PackedSite) : Bool :=
  (ss.length == 8) && (ss.zipIdx.all fun (s,i) => s.spec == inputSpec a i)

end AKLT.Cert.H1.Production
