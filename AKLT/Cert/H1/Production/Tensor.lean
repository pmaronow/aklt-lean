import AKLT.Cert.H1.Production.Semantics

/-! Polynomial intermediate separating moment/Fubini refinement from Pauli
basis substitution. It is not certificate data and contains no proof. -/
namespace AKLT.Cert.H1.Production
open AKLT.Defs
noncomputable section

abbrev VectorPolynomial := MvPolynomial (Fin 20 × Fin 3) ℚ
abbrev PolyFour := List (List VectorPolynomial)

def vectorVariable (token color : Nat) : VectorPolynomial :=
  MvPolynomial.X (⟨token%20,Nat.mod_lt _ (by decide)⟩,
    ⟨(color-1)%3,Nat.mod_lt _ (by decide)⟩)

def vectorMonomial (token : Nat) : List Nat → VectorPolynomial
  | [] => 1
  | c :: cs => (if c == 0 then 1 else vectorVariable token c) * vectorMonomial (token+1) cs

def localPolynomial (site : Nat) (s : SiteSpec) (l r v : Nat) : VectorPolynomial :=
  if (!s.left && l != 0) || (!s.right && r != 0) || (!s.center && v != 0) then 0
  else if s.leaf then
    let label := if s.left then l else r
    let sc : Int := if label == 0 then s.den else if s.inverted then -1 else 1
    MvPolynomial.C (sc : ℚ) * (if label == 0 then 1 else vectorVariable (ringLeader site) label)
  else
    ((colorChoices s.nslots).map fun cs =>
      let colors := (if s.left then [l] else []) ++ (if s.right then [r] else []) ++
        (if s.center then [v] else []) ++ cs
      let mom := momentNumerator s.den s.diluted
        (countColor 1 colors) (countColor 2 colors) (countColor 3 colors)
      let tip : Int := if s.tip then if cs.headD 0 == 0 then 5 else 3 else 1
      let sign : Int := if s.inverted && (cs.filter (· != 0)).length % 2 == 1 then -1 else 1
      MvPolynomial.C ((mom*tip*sign : Int) : ℚ) * vectorMonomial (ringLeader site) cs).sum

def polyEntry (m : PolyFour) (i j : Nat) : VectorPolynomial := (m.getD i []).getD j 0

def polyIdentity : PolyFour := (List.range 4).map (fun i =>
  (List.range 4).map (fun j => if i == j then 1 else 0))

def polyMul (a b : PolyFour) : PolyFour :=
  (List.range 4).map (fun i => (List.range 4).map (fun j =>
    ((List.range 4).map (fun k => polyEntry a i k * polyEntry b k j)).sum))

def polyTrace (a : PolyFour) : VectorPolynomial :=
  ((List.range 4).map (fun i => polyEntry a i i)).sum

def polynomialRingProduct (site : Nat) : List PackedSite → List Nat → PolyFour
  | [], _ => polyIdentity
  | s :: ss, codes => polyMul
      ((List.range 4).map (fun l => (List.range 4).map (fun r =>
        localPolynomial site s.spec l r (codes.headD 0))))
      (polynomialRingProduct (site+1) ss codes.tail)

def polynomialRingValue (ss : List PackedSite) (codes : List Nat) : VectorPolynomial :=
  polyTrace (polynomialRingProduct 0 ss codes)

def networkNumerator (ss : List PackedSite) (out : Nat) (next : Bool) : VectorPolynomial :=
  let Z := polynomialRingValue ss []
  let terms := (centerPairs ss).filterMap fun (x,y) =>
    if next && (x == out || y == out) then none else
      some (((List.range 3).map (fun k =>
        polynomialRingValue ss (centerCodes ss.length x y (k+1)))).sum)
  MvPolynomial.C (if next then 5 else 3) * Z + terms.sum

end
end AKLT.Cert.H1.Production
