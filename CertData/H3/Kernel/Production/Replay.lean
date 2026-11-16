import CertData.H3.Kernel.Production.Model
import CertData.H3.Kernel.PrefixView

namespace AKLT.Cert.H3.Production

structure Exact where
  denominator : Nat
  straight : Nat
  turn : Nat
  third : Nat
  fifth : Nat
  reward : Nat → Nat → Nat → Nat
  response : Nat → Nat → Nat → Nat

structure RewardItem where
  straight : Bool
  reward : Nat
  time : Nat
  deriving Inhabited

structure PrefixState where
  walk : Walk
  A : Nat
  B : Nat
  C : Nat
  D : Nat
  base : Nat
  items : List RewardItem
  deriving Inhabited

def initial : PrefixState := ⟨prefixInitial,1,1,0,0,1,[]⟩
def departures (w : Walk) (x : Point) : Nat := (w.departed.filter (fun y => y == x)).length
def deadMaskAt (w : Walk) : Nat := dirs.foldl (fun mask d =>
  let x := advance w.pos d
  if x=(0,0) ∨ 2≤departures w x then mask+2^d else mask) 0

def transition (E : Exact) (s : PrefixState) (d : Nat) : PrefixState :=
  let w := s.walk
  let next := w.step d
  if w.departed.contains w.pos then
    ⟨next,s.A*E.fifth,s.B*E.fifth,s.C*E.fifth,s.D*E.fifth,s.base*E.fifth,s.items⟩
  else
    let mask := deadMaskAt w
    let reward := E.reward w.incoming d mask
    let response := E.response w.incoming d mask
    let item : RewardItem := ⟨d==w.incoming,reward,w.depth⟩
    if d=w.incoming then
      ⟨next,s.A*E.straight,s.B*E.straight,s.C*E.straight,
        s.D*E.third+s.B*response,s.base*E.third,item::s.items⟩
    else
      ⟨next,s.A*E.turn,s.B*E.third,s.C*E.third+s.A*response,
        s.D*E.third,s.base*E.third,item::s.items⟩

def exposureFactor (E : Exact) (i : RewardItem) : Nat :=
  if i.straight then E.straight*3 else E.turn*3
def itemLE (E : Exact) (i j : RewardItem) : Bool :=
  if i.reward=0 then decide (j.reward=0 ∧ i.time≤j.time)
  else if j.reward=0 then true else
    let xi := exposureFactor E i
    let xj := exposureFactor E j
    let lhs := (xi-E.denominator)*xj*j.reward
    let rhs := (xj-E.denominator)*xi*i.reward
    decide (lhs<rhs ∨ (lhs=rhs ∧ i.time≤j.time))

/-- Numerator at denominator K^(2*length), with exact order computed in Lean. -/
def exposureNumerator (E : Exact) : List RewardItem → Nat
  | [] => 0
  | i::rest => exposureFactor E i *
      (i.reward*E.denominator^(2*rest.length)+E.denominator*exposureNumerator E rest)

/-- Short contributions use the fixed denominator K^36 for all lengths ≤12. -/
def shortValue (E : Exact) (s : PrefixState) : Nat :=
  let sorted := mergeSortFuel (itemLE E) s.items.length s.items
  s.base * exposureNumerator E sorted * E.denominator^(36-(s.walk.depth+2*sorted.length))

structure PrefixResult where
  tail : Nat
  short : Nat
  leaves : Nat
  closed : Nat
  nodes : Nat
  stems : Nat
  ok : Bool
  deriving DecidableEq, Repr
def zeroResult : PrefixResult := ⟨0,0,0,0,0,0,true⟩
def PrefixResult.add (a b : PrefixResult) : PrefixResult :=
  ⟨a.tail+b.tail,a.short+b.short,a.leaves+b.leaves,a.closed+b.closed,
    a.nodes+b.nodes,a.stems+b.stems,a.ok && b.ok⟩
def target (X : AKLT.Defs.PairType) : Point := match X with | .B => (1,0) | .C => (0,1)
def goodStep (d₀ : Nat) (w : Walk) (d : Nat) : Bool :=
  (w.depth != 0 || d == d₀) && w.legal d && (advance w.pos d != (0,0))

def endpointValue (T : Tables) (p a : Nat) (x : Point) : Nat :=
  AKLT.Gen.Packed.lane (T.endpoint (phaseKey p a)) 80 (endpointIndex x)

def leafValue (G : Graph) (T : Tables) (s : PrefixState) : PrefixResult :=
  let a := G.classAt s.walk.code
  ⟨s.A*endpointValue T 0 a s.walk.pos+s.B*endpointValue T 1 a s.walk.pos+
    s.C*endpointValue T 2 a s.walk.pos+s.D*endpointValue T 3 a s.walk.pos,
    0,1,0,1,0,decide (a<3741) && endpointInside s.walk.pos⟩

def prefixDFS (G : Graph) (T : Tables) (E : Exact) (X : AKLT.Defs.PairType) (d₀ : Nat) :
    Nat → PrefixState → PrefixResult
  | 0, s => if s.walk.pos=target X then ⟨0,shortValue E s,0,1,1,0,true⟩ else leafValue G T s
  | n+1, s =>
    if s.walk.pos=target X then ⟨0,shortValue E s,0,1,1,0,true⟩ else
    let children := (dirs.map fun d =>
      if goodStep d₀ s.walk d then prefixDFS G T E X d₀ n (transition E s d) else zeroResult).foldl PrefixResult.add zeroResult
    {children with nodes := children.nodes+1}

def replayPrefix (E : Exact) (X : AKLT.Defs.PairType) (d₀ : Nat) :
    Nat → Nat → PrefixState → Option PrefixState
  | 0, _, s => if s.walk.pos=target X then none else some s
  | n+1, code, s =>
    if s.walk.pos=target X then none else
    let d := code / 4^n % 4
    if goodStep d₀ s.walk d then replayPrefix E X d₀ n code (transition E s d) else none

/-- Exhaust all code slots, including invalid stems, so scheduling does not supply coverage. -/
def prefixStem (G : Graph) (T : Tables) (E : Exact) (X : AKLT.Defs.PairType) (d₀ depth code : Nat) : PrefixResult :=
  match replayPrefix E X d₀ depth code initial with
  | none => zeroResult
  | some s => let r := prefixDFS G T E X d₀ (12-depth) s; {r with stems := 1}
def prefixBatch (G : Graph) (T : Tables) (E : Exact) (X : AKLT.Defs.PairType)
    (d₀ depth start count : Nat) : PrefixResult :=
  ((List.range count).map fun i => prefixStem G T E X d₀ depth (start+i)).foldl PrefixResult.add zeroResult

/-- Early hits are counted through the frontier; surviving frontier states contribute zero. -/
def earlyDFS (E : Exact) (X : AKLT.Defs.PairType) (d₀ : Nat) : Nat → PrefixState → PrefixResult
  | 0, s => if s.walk.pos=target X then ⟨0,shortValue E s,0,1,1,0,true⟩ else {zeroResult with nodes := 1}
  | n+1, s =>
    if s.walk.pos=target X then ⟨0,shortValue E s,0,1,1,0,true⟩ else
    let r := (dirs.map fun d => if goodStep d₀ s.walk d then earlyDFS E X d₀ n (transition E s d) else zeroResult).foldl PrefixResult.add zeroResult
    {r with nodes := r.nodes+1}

def finalNumerator (E : Exact) (r : PrefixResult) : Nat :=
  r.short*65536+r.tail*E.denominator^24
def finalDenominator (E : Exact) : Nat := E.denominator^36*65536
def ceilingCheck (E : Exact) (r : PrefixResult) (ceiling : Nat) : Bool :=
  r.ok && decide (10^9*finalNumerator E r ≤ ceiling*finalDenominator E)

end AKLT.Cert.H3.Production
