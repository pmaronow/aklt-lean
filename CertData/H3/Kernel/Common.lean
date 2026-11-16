import AKLT.Defs.Computational
import AKLT.Gen.Packed.All

namespace AKLT.Cert.H3
open AKLT.Defs AKLT.Gen.Packed

def direction : Nat → Compass
  | 0 => .east | 1 => .north | 2 => .west | _ => .south
def directionCode : Compass → Nat
  | .east => 0 | .north => 1 | .west => 2 | .south => 3
def phaseCode : Phase → Nat
  | .A => 0 | .B => 1 | .C => 2 | .D => 3
def stepKind : Nat → StepKind
  | 0 => .straight | 1 => .turn | _ => .revisit
def decodeWord (m code : Nat) : DirectionWord m :=
  fun i => direction ((code / 4^(m-1-i.val)) % 4)
def encodeWord {m : Nat} (w : DirectionWord m) : Nat :=
  ((List.finRange m).map fun i => directionCode (w i) * 4^(m-1-i.val)).sum

def width : Nat := 141
def cells : Nat := 19881
def bits : Nat := 80
def guardBit : Nat := 79
def coefficientScale : Nat := 281474976710656
def valueScale : Nat := 65536
def gridSite (s : Nat) : Plane := ((s / 141 : Nat) - (70 : Int), (s % 141 : Nat) - (70 : Int))
def siteIndex (x : Plane) : Nat := (x.1 + 70).toNat * 141 + (x.2 + 70).toNat

/-- A balanced, sparse lookup tree. Missing data have value zero. -/
inductive PlaneTree where
  | empty
  | leaf (key value : Nat)
  | branch (pivot : Nat) (left right : PlaneTree)
def PlaneTree.get : PlaneTree → Nat → Nat
  | .empty, _ => 0
  | .leaf k v, j => if j = k then v else 0
  | .branch p l r, j => if j < p then l.get j else r.get j

/-- The exact component row occurring in `StationaryData.Passes`. -/
def DefRow {m q : Nat} (Q : MemoryQuotient m q) (C : StationaryData q)
    (X : PairType) (d₀ : Compass) (φ : Phase) (a : Fin q) (x : Plane) : Prop :=
  (∑ d : Compass, ∑ ψ : Phase,
    coefficientCeiling (stationaryCoefficient Q X d₀ φ a x d ψ) *
      C.extended ψ (Q.successor a d) (x + d.step)) ≤
        certificateCoefficientScale * C.extended φ a x

end AKLT.Cert.H3
