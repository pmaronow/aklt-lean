import AKLT.Defs.OperatorContracts
import AKLT.Gen.Gram.Basic

/-! A signed Kronecker-packed ring constructor. All executable arithmetic is
Nat/Int, with structural list recursion. Its refinement to reducedPolynomial
is specified separately in Obligations. -/
namespace AKLT.Cert.H1

structure Gaussian where
  re : Int
  im : Int
  deriving DecidableEq, BEq, Repr

def Gaussian.zero : Gaussian := ⟨0, 0⟩
def Gaussian.one : Gaussian := ⟨1, 0⟩
def Gaussian.add (a b : Gaussian) : Gaussian := ⟨a.re + b.re, a.im + b.im⟩
def Gaussian.scale (n : Int) (a : Gaussian) : Gaussian := ⟨n * a.re, n * a.im⟩
def Gaussian.mul (a b : Gaussian) : Gaussian :=
  if a == .zero || b == .zero then .zero
  else ⟨a.re*b.re - a.im*b.im, a.re*b.im + a.im*b.re⟩

/-- Balanced lookup, used for local tensors (up to 1024 integer pairs). -/
inductive Table where
  | empty
  | leaf (a : Gaussian)
  | node (cut : Nat) (left right : Table)
  deriving DecidableEq, BEq

def Table.get : Table → Nat → Gaussian
  | .empty, _ => .zero
  | .leaf a, i => if i == 0 then a else .zero
  | .node cut l r, i => if i < cut then l.get i else r.get (i-cut)

def pauliZ (a i j : Nat) : Gaussian :=
  if a == 0 then ⟨if i == j then 1 else 0, 0⟩
  else if a == 1 then ⟨if i == j then 0 else 1, 0⟩
  else if a == 2 then ⟨0, if i == j then 0 else if i == 0 then -1 else 1⟩
  else ⟨if i != j then 0 else if i == 0 then 1 else -1, 0⟩

def basisPair : Nat → List (Nat × Nat × Int)
  | 0 => [(0, 0, 1)]
  | 1 => [(0, 1, 1), (1, 0, 1)]
  | 2 => [(1, 1, 1)]
  | _ => [(0, 1, 1), (1, 0, -1)]

def sumGaussian : List Gaussian → Gaussian
  | [] => .zero
  | a :: as => a.add (sumGaussian as)

def pairForm (c e a b : Nat) : Gaussian :=
  sumGaussian ((basisPair a).flatMap fun (i,j,u) =>
    (basisPair b).map fun (k,l,v) => ((pauliZ c i k).mul (pauliZ e j l)).scale (u*v))

def countColor (k : Nat) : List Nat → Nat
  | [] => 0
  | a :: as => (if a == k then 1 else 0) + countColor k as

/-- Numerator of the degree-four moment, at a supplied valid denominator. -/
def momentNumerator (den : Nat) (diluted : Bool) (a b c : Nat) : Int :=
  if a % 2 != 0 || b % 2 != 0 || c % 2 != 0 then 0
  else if a+b+c == 0 then den
  else if a+b+c == 2 then den / (if diluted then 5 else 3)
  else if a+b+c == 4 then
    if a == 4 || b == 4 || c == 4 then
      if diluted then 3 * (den / 25) else den / 5
    else den / (if diluted then 25 else 15)
  else 0

def siteLCD (degree : Nat) (diluted : Bool) : Nat :=
  if degree < 2 then 1 else if degree < 4 then (if diluted then 5 else 3)
  else (if diluted then 25 else 15)

structure SiteSpec where
  dim : Nat
  left : Bool
  right : Bool
  center : Bool
  nslots : Nat
  diluted : Bool
  leaf : Bool
  tip : Bool
  inverted : Bool
  stride : Nat
  deriving DecidableEq, BEq, Repr

def SiteSpec.den (s : SiteSpec) : Nat :=
  if s.leaf then (if s.diluted then 3 else 2)
  else siteLCD (s.left.toNat+s.right.toNat+s.center.toNat+s.nslots) s.diluted

def SiteSpec.totalDen (s : SiteSpec) : Nat := s.den * (if s.tip then 5 else 1)

def colorChoices : Nat → List (List Nat)
  | 0 => [[]]
  | n+1 => (List.range 4).flatMap fun a => (colorChoices n).map (a :: ·)

def localForm (cs : List Nat) (a b : Nat) : Gaussian :=
  match cs with
  | [] => .one
  | [c] => pauliZ c a b
  | c :: e :: _ => pairForm c e a b

/-- Direct moment contraction and local Pauli substitution at one site. -/
def localEntry (s : SiteSpec) (a l r v b : Nat) : Gaussian :=
  if (!s.left && l != 0) || (!s.right && r != 0) || (!s.center && v != 0) then .zero
  else if s.leaf then
    let label := if s.left then l else r
    let sc : Int := if label == 0 then s.den else if s.inverted then -1 else 1
    (pauliZ label a b).scale sc
  else
    sumGaussian ((colorChoices s.nslots).map fun cs =>
      let colors := (if s.left then [l] else []) ++ (if s.right then [r] else []) ++
        (if s.center then [v] else []) ++ cs
      let mom := momentNumerator s.den s.diluted
        (countColor 1 colors) (countColor 2 colors) (countColor 3 colors)
      let tipScale : Int := if s.tip then if cs.headD 0 == 0 then 5 else 3 else 1
      let sign : Int := if s.inverted && (cs.filter (· != 0)).length % 2 == 1 then -1 else 1
      (localForm cs a b).scale (mom * tipScale * sign))

def tableIndex (dim a l r v b : Nat) : Nat := ((((a*4+l)*4+r)*4+v)*dim+b)

def localTable (s : SiteSpec) : List Gaussian :=
  (List.range s.dim).flatMap fun a => (List.range 4).flatMap fun l =>
    (List.range 4).flatMap fun r => (List.range 4).flatMap fun v =>
      (List.range s.dim).map fun b => localEntry s a l r v b

/-- The table is auxiliary certificate data, independently reconstructed locally. -/
def tableCheck (s : SiteSpec) (t : Table) : Bool :=
  ((localTable s).zipIdx).all fun (v,i) => decide (t.get i = v)

structure PackedSite where
  spec : SiteSpec
  table : Table

def packGaussian (base : Int) : List Gaussian → Gaussian
  | [] => .zero
  | a :: as => a.add ((packGaussian base as).scale base)

abbrev FourMatrix := List (List Gaussian)

def matrixEntry (m : FourMatrix) (i j : Nat) : Gaussian := (m.getD i []).getD j .zero

def fourIdentity : FourMatrix := (List.range 4).map fun i =>
  (List.range 4).map fun j => if i == j then .one else .zero

def fourMul (a b : FourMatrix) : FourMatrix :=
  (List.range 4).map fun i => (List.range 4).map fun j =>
    sumGaussian ((List.range 4).map fun k => (matrixEntry a i k).mul (matrixEntry b k j))

def fourTrace (a : FourMatrix) : Gaussian :=
  sumGaussian ((List.range 4).map fun i => matrixEntry a i i)

def siteMatrix (s : PackedSite) (row v width : Nat) : FourMatrix :=
  let a := row / s.spec.stride % s.spec.dim
  let base : Int := (2 : Nat) ^ (width * s.spec.stride)
  (List.range 4).map fun l => (List.range 4).map fun r =>
    packGaussian base ((List.range s.spec.dim).map fun b =>
      s.table.get (tableIndex s.spec.dim a l r v b))

/-- Center codes have one fixed color per ring site. -/
def ringProduct (row width : Nat) : List PackedSite → List Nat → FourMatrix
  | [], _ => fourIdentity
  | s :: ss, codes => fourMul (siteMatrix s row (codes.headD 0) width)
      (ringProduct row width ss codes.tail)

def ringValue (ss : List PackedSite) (row width : Nat) (codes : List Nat) : Gaussian :=
  fourTrace (ringProduct row width ss codes)

def centerCodes (n x y k : Nat) : List Nat :=
  (List.range n).map fun i => if i == x || i == y then k else 0

def centerPairs (ss : List PackedSite) : List (Nat × Nat) :=
  let ids := ((List.range ss.length).zip ss).filterMap fun (i,s) => if s.spec.center then some i else none
  ids.flatMap fun x => ids.filterMap fun y => if x < y then some (x,y) else none

/-- Full threshold row as a polynomial evaluated at the packing base. -/
def packedThresholdRow (ss : List PackedSite) (out row width p q : Nat) : Gaussian :=
  let Z := ringValue ss row width []
  let terms := (centerPairs ss).map fun (x,y) =>
    (x,y,sumGaussian ((List.range 3).map fun k =>
      ringValue ss row width (centerCodes ss.length x y (k+1))))
  let cur := (Z.scale 3).add (sumGaussian (terms.map fun (_,_,c) => c))
  let nxt := (Z.scale 5).add (sumGaussian (terms.filterMap fun (x,y,c) =>
    if x != out && y != out then some c else none))
  (cur.scale (5*q)).add (nxt.scale (-(3*(p : Int))))

/-- Uniform signed-digit bias. The coefficient bound must be justified separately. -/
def signedBias (width lanes : Nat) : Int :=
  (((2 : Nat) ^ (width*lanes)-1) / ((2 : Nat)^width-1) * (2 : Nat)^(width-1) : Nat)

def signedDigit (packed : Int) (width index : Nat) : Int :=
  packed / ((2 : Nat)^(width*index) : Int) % ((2 : Nat)^width : Int) - ((2 : Nat)^(width-1) : Int)

def constructedRow (ss : List PackedSite) (out width lanes p q row : Nat) (indices : List Nat) : List Int :=
  let packed := (packedThresholdRow ss out row width p q).re + signedBias width lanes
  indices.map fun j => signedDigit packed width j

def constructedRows (ss : List PackedSite) (out width lanes p q : Nat) (indices : List Nat) :
    List (List Int) := indices.map fun i => constructedRow ss out width lanes p q i indices

end AKLT.Cert.H1
