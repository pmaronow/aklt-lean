import Mathlib
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace CompfeasGeometry
abbrev Point := Int × Int
def eqP (a b : Point) : Bool := a.1 == b.1 && a.2 == b.2
def move (p : Point) (d : Nat) : Point :=
  match d with
  | 0 => (p.1+1,p.2)
  | 1 => (p.1,p.2+1)
  | 2 => (p.1-1,p.2)
  | _ => (p.1,p.2-1)
def used (es : List (Point × Point)) (a b : Point) : Bool :=
  es.any (fun e => (eqP e.1 a && eqP e.2 b) || (eqP e.1 b && eqP e.2 a))
def leaves : Nat → Point → List (Point × Point) → Nat
  | 0, p, _ => if eqP p (1,0) then 0 else 1
  | n+1, p, es =>
    if eqP p (1,0) then 0 else
      [0,1,2,3].foldl (fun acc d =>
        let q := move p d
        if eqP q (0,0) || used es p q then acc
        else acc + leaves n q ((p,q)::es)) 0
theorem checked : leaves 7 (-1,1) [((-1,0),(-1,1))] = 1466 := by decide +kernel
#print axioms checked
end CompfeasGeometry
