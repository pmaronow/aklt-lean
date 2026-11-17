module
public import CertData.H3.Kernel.Rows

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

/-! Executable, data-independent production interface. Soundness is supplied by
closed leaves, not by assertions in this implementation. -/
namespace AKLT.Cert.H3.Production
open AKLT.Defs AKLT.Gen.Packed

abbrev Point := Int × Int
abbrev Bond := Point × Point
def dirs : List Nat := [0,1,2,3]
def delta : Nat → Point
  | 0 => (1,0) | 1 => (0,1) | 2 => (-1,0) | _ => (0,-1)
def advance (x : Point) (d : Nat) : Point := (x.1+(delta d).1,x.2+(delta d).2)
def rev (d : Nat) : Nat := (d+2)%4
def bond (x y : Point) : Bond := if x.1 < y.1 ∨ (x.1=y.1 ∧ x.2≤y.2) then (x,y) else (y,x)
def phase : Nat → Phase
  | 0 => .A | 1 => .B | 2 => .C | _ => .D
def finState (a : Nat) : Fin 3741 := ⟨a%3741,Nat.mod_lt _ (Nat.succ_pos 3740)⟩
def phaseKey (p a : Nat) : Nat := p*3741+a

structure Graph where
  classAt : Nat → Nat
  classSpan : Nat → Nat → Nat
  representative : Nat → Nat
  dest : Nat → Nat → Nat
  kind : Nat → Nat → Nat

def Graph.allowed (G : Graph) (a d : Nat) : Bool := G.dest a d != 0
def Graph.next (G : Graph) (a d : Nat) : Nat := (G.dest a d-1)%3741
def Graph.arrival (G : Graph) (a : Nat) : Nat := G.representative a % 4
def Graph.quotient (G : Graph) : MemoryQuotient 10 3741 where
  project w := finState (G.classAt (encodeWord w))
  representative a := decodeWord 10 (G.representative a.val)
  allowed a d := G.allowed a.val (directionCode d)
  kind a d := stepKind (G.kind a.val (directionCode d))
  successor a d := finState (G.next a.val (directionCode d))
  arrival a := direction (G.arrival a.val)

structure Tables where
  plane : Nat → Nat
  cap : Nat → Nat
  endpoint : Nat → Nat

def Tables.planeFn (T : Tables) (φ : Phase) (a : Fin 3741) : Nat := T.plane (phaseKey (phaseCode φ) a.val)
def Tables.capFn (T : Tables) (φ : Phase) (a : Fin 3741) : Nat := T.cap (phaseKey (phaseCode φ) a.val)
def Tables.data (T : Tables) : StationaryData 3741 where
  cap := T.capFn
  value φ a x := lane (T.planeFn φ a) 80 (siteIndex x.val)

/-- Rectangle [-13,11] × [-12,12], containing both endpoint parities. -/
def endpointIndex (x : Point) : Nat := (x.1+13).toNat*25+(x.2+12).toNat
def endpointInside (x : Point) : Bool := decide (-13≤x.1 ∧ x.1≤11 ∧ -12≤x.2 ∧ x.2≤12)
def rectangle (P : Nat) : Nat :=
  (List.range 25).foldr (fun r rest =>
    Nat.land (P >>> (80*((r+57)*141+58))) (2^(80*25)-1) + (rest <<< (80*25))) 0

def freeRow (G : Graph) (T : Tables) (p a : Nat) : Nat :=
  (dirs.map fun d =>
    if !G.allowed a d then 0 else
    let t := G.next a d
    let k := G.kind a d
    let diag := diagonal (phase p) (stepKind k) * T.cap (phaseKey p t)
    diag + if (p=0 ∧ k=1) ∨ (p=1 ∧ k=0) then
      response (G.arrival a) d 4 * T.cap (phaseKey (if k=1 then 2 else 3) t) else 0).sum

def planeCheck (G : Graph) (T : Tables) (X : PairType) (d₀ : Compass) (key : Nat) : Bool :=
  let p := key/3741
  let a := key%3741
  let U := T.plane key
  let Z := T.cap key
  localRowCheck G.quotient T.planeFn T.capFn X d₀ (phase p) (finState a) &&
  packedRowCheck 79 19881 26 1 (repeatLane 80 19881 Z) [(1,U)] &&
  decide (0<Z ∧ Z<2^26) && decide (p<2 ∨ 65536≤Z) &&
  decide (lane U 80 (siteIndex kernelCentre)=0) &&
  decide (lane U 80 (siteIndex (kernelTarget X))=(if p<2 then 0 else 65536)) &&
  decide (freeRow G T p a ≤ coefficientScale*Z) &&
  (rectangle U == T.endpoint key)

def planeBatch (G : Graph) (T : Tables) (X : PairType) (d₀ : Compass) (start count : Nat) : Bool :=
  (List.range count).all (fun i => planeCheck G T X d₀ (start+i))

structure Walk where
  pos : Point
  incoming : Nat
  used : List Bond
  departed : List Point
  code : Nat
  depth : Nat
  deriving Inhabited

def rawInitial : Walk := ⟨(0,0),0,[],[],0,0⟩
def prefixInitial : Walk := ⟨(-1,0),2,[],[],0,0⟩
def Walk.step (w : Walk) (d : Nat) : Walk :=
  let y := advance w.pos d
  ⟨y,d,bond w.pos y :: w.used,w.pos :: w.departed,(w.code*4+d)%1048576,w.depth+1⟩
def Walk.legal (w : Walk) (d : Nat) : Bool := !(w.used.contains (bond w.pos (advance w.pos d)))
def replayRaw : Nat → Nat → Walk → Option Walk
  | 0, _, w => some w
  | n+1, code, w =>
    let d := (code / 4^n)%4
    if w.legal d then replayRaw n code (w.step d) else none

def rawRow (G : Graph) (w : Walk) : Bool :=
  let a := G.classAt w.code
  let revisit := w.departed.contains w.pos
  decide (a<3741) && dirs.all (fun d =>
    let allowed := (d != rev w.incoming) && w.legal d
    (G.allowed a d == allowed) &&
    (!allowed || (decide (G.dest a d ≤ 3741) &&
      (G.kind a d == if revisit then 2 else if d=w.incoming then 0 else 1) &&
      (G.next a d == G.classAt ((w.code*4+d)%1048576)) &&
      (revisit || G.arrival a == w.incoming))))

structure RawStats where
  count : Nat
  ok : Bool
  deriving DecidableEq, Repr
def RawStats.add (a b : RawStats) : RawStats := ⟨a.count+b.count,a.ok && b.ok⟩
def rawDFS (G : Graph) : Nat → Walk → RawStats
  | 0, w => ⟨1,rawRow G w⟩
  | n+1, w => (dirs.map fun d => if w.legal d then rawDFS G n (w.step d) else
      ⟨0,G.classSpan ((w.code*4+d)*4^n) (4^n) == repeatLane 12 (4^n) 3741⟩).foldl RawStats.add ⟨0,true⟩
def rawStem (G : Graph) (code : Nat) : RawStats :=
  match replayRaw 6 code rawInitial with
  | none => ⟨0,G.classSpan (code*256) 256 == repeatLane 12 256 3741⟩
  | some w => rawDFS G 4 w
def rawBatch (G : Graph) (start count : Nat) : RawStats :=
  ((List.range count).map fun i => rawStem G (start+i)).foldl RawStats.add ⟨0,true⟩
def representativeCheck (G : Graph) (a : Nat) : Bool :=
  decide (G.representative a < 1048576) &&
  match replayRaw 10 (G.representative a) rawInitial with
  | none => false
  | some w => G.classAt w.code == a
def representativeBatch (G : Graph) (start count : Nat) : Bool :=
  (List.range count).all (fun i => representativeCheck G (start+i))
def fieldCheck (G : Graph) (a : Nat) : Bool := dirs.all (fun d =>
  decide (G.dest a d ≤ 3741 ∧ (G.dest a d=0 ↔ G.kind a d=3) ∧
    (G.dest a d ≠ 0 → G.kind a d<3)))
def fieldBatch (G : Graph) (start count : Nat) : Bool :=
  (List.range count).all (fun i => fieldCheck G (start+i))
def edgeCounts (G : Graph) : Nat × Nat × Nat :=
  (List.range 3741).foldl (fun acc a => dirs.foldl (fun acc d =>
    if !G.allowed a d then acc else
    match G.kind a d with
    | 0 => (acc.1+1,acc.2.1,acc.2.2)
    | 1 => (acc.1,acc.2.1+1,acc.2.2)
    | _ => (acc.1,acc.2.1,acc.2.2+1)) acc) (0,0,0)

end AKLT.Cert.H3.Production
