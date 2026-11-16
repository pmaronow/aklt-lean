from pathlib import Path
root=Path(__file__).resolve().parents[1]
head='''import Mathlib
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
'''
dx=[1,0,-1,0];dy=[0,1,0,-1]
def count(n,p,es):
 if p==(1,0):return 0
 if n==0:return 1
 ans=0
 for d in range(4):
  q=(p[0]+dx[d],p[1]+dy[d]);e=tuple(sorted((p,q)))
  if q==(0,0) or e in es:continue
  es.add(e);ans+=count(n-1,q,es);es.remove(e)
 return ans
for L in [8,10,12,14]:
 expected=count(L-1,(-1,1),{((-1,0),(-1,1))})
 if L==12:assert expected==89150
 if L==14:assert expected==688590
 body=head+f'theorem checked : leaves {L-1} (-1,1) [((-1,0),(-1,1))] = {expected} := by decide +kernel\n#print axioms checked\nend CompfeasGeometry\n'
 (root/'probes'/f'PrefixLeaves{L}.lean').write_text(body)
 print(L,expected)
