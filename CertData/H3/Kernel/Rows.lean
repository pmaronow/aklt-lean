import CertData.H3.Kernel.Packed

namespace AKLT.Cert.H3
open AKLT.Defs AKLT.Gen.Packed

def allMask : Nat := 2^(80*19881)-1
def oneMask (s : Nat) : Nat := (2^80-1) <<< (80*s)
def firstColumn : Nat := repeatLane (80*141) 141 (2^80-1)
def lastColumn : Nat := firstColumn <<< (80*140)
def firstRow : Nat := 2^(80*141)-1
def lastRow : Nat := firstRow <<< (80*(19881-141))
def boundaryMask : Compass → Nat
  | .east => lastRow | .north => lastColumn | .west => firstRow | .south => firstColumn

/-- Pull values from `x+d`, with a cap on the missing boundary; never wrap. -/
def pull (P Z : Nat) (d : Compass) : Nat :=
  let shifted := match d with
    | .east => P >>> (80*141) | .north => P >>> 80
    | .west => P <<< (80*141) | .south => P <<< 80
  Nat.land shifted (allMask - boundaryMask d) +
    Nat.land (repeatLane 80 19881 Z) (boundaryMask d)

def ordinaryMask (X : PairType) (d₀ : Compass) : Nat :=
  allMask - oneMask (siteIndex kernelCentre) - oneMask (siteIndex (kernelTarget X)) -
    oneMask (siteIndex kernelStart) - oneMask (siteIndex (kernelStart+d₀.step))
def knownMask (d₀ d : Compass) : Nat :=
  (if d = d₀ then 0 else oneMask (siteIndex kernelStart)) +
  (if d = d₀.reverse then 0 else oneMask (siteIndex (kernelStart+d₀.step)))
def centreNeighbourMask (j : Nat) : Nat := oneMask (siteIndex (-(direction j).step))
def centreNeighbourMasks : Nat := (List.range 4).foldl (fun a j => a + centreNeighbourMask j) 0
def deadMask (j : Nat) : Nat :=
  if j < 4 then centreNeighbourMask j else allMask - centreNeighbourMasks

def qs : Nat := 97632666219444
def qt : Nat := 100347585280092
def q3 : Nat := 93824992236886
def q5 : Nat := 56294995342132
def diagonal (φ : Phase) (k : StepKind) : Nat :=
  if k = .revisit then q5 else match φ,k with
    | .A,.straight | .B,.straight | .C,.straight => qs
    | .A,.turn => qt | _,_ => q3
def responseTable : List (List (List Nat)) := [
  [[96841236300536,39835065091129,96841236300536,39835065091129,96841236300536],
   [34585899090222,96996758642902,96996758642902,41503078908266,96996758642902],
   [0,0,0,0,0], [34585899090222,41503078908266,96996758642902,96996758642902,96996758642902]],
  [[96996758642902,34585899090222,41503078908266,96996758642902,96996758642902],
   [39835065091129,96841236300536,39835065091129,96841236300536,96841236300536],
   [41503078908266,34585899090222,96996758642902,96996758642902,96996758642902], [0,0,0,0,0]],
  [[0,0,0,0,0], [96996758642902,96996758642902,34585899090222,41503078908266,96996758642902],
   [96841236300536,39835065091129,96841236300536,39835065091129,96841236300536],
   [96996758642902,41503078908266,34585899090222,96996758642902,96996758642902]],
  [[96996758642902,96996758642902,41503078908266,34585899090222,96996758642902], [0,0,0,0,0],
   [41503078908266,96996758642902,96996758642902,34585899090222,96996758642902],
   [39835065091129,96841236300536,39835065091129,96841236300536,96841236300536]]]
def response (ain d j : Nat) : Nat := (((responseTable[ain]?.getD [])[d]?.getD [])[j]?.getD 0)

/-- Construct actual routed/masked terms, rather than reading a supplied row matrix. -/
def rowTerms {m q : Nat} (Q : MemoryQuotient m q)
    (plane cap : Phase → Fin q → Nat) (X : PairType) (d₀ : Compass) (φ : Phase) (a : Fin q) : List PackedTerm :=
  [Compass.east,.north,.west,.south].flatMap fun d =>
    if !Q.allowed a d then [] else
    let t := Q.successor a d
    let k := Q.kind a d
    let p := pull (plane φ t) (cap φ t) d
    let ordinary := ordinaryMask X d₀
    let diag := [(diagonal φ k, Nat.land p ordinary)]
    let known := if k = .revisit then [] else [(q5, Nat.land p (knownMask d₀ d))]
    let resp := if (φ = .A ∧ k = .turn) ∨ (φ = .B ∧ k = .straight) then
      let ψ := if k = .turn then Phase.C else Phase.D
      let v := pull (plane ψ t) (cap ψ t) d
      (List.range 5).map fun j => (response (directionCode (Q.arrival a)) (directionCode d) j,
        Nat.land v (Nat.land ordinary (deadMask j)))
      else []
    diag ++ known ++ resp

def localRowCheck {m q : Nat} (Q : MemoryQuotient m q)
    (plane cap : Phase → Fin q → Nat) (X : PairType) (d₀ : Compass) (φ : Phase) (a : Fin q) : Bool :=
  packedRowCheck 79 19881 26 coefficientScale (plane φ a) (rowTerms Q plane cap X d₀ φ a)

theorem localRowCheck_sound {m q : Nat} {Q : MemoryQuotient m q}
    {plane cap : Phase → Fin q → Nat} {X : PairType} {d₀ : Compass} {φ : Phase} {a : Fin q}
    (h : localRowCheck Q plane cap X d₀ φ a = true) :
    ∀ s < 19881, component 80 s (rowTerms Q plane cap X d₀ φ a) ≤
      coefficientScale * lane (plane φ a) 80 s := packedRowCheck_sound h

/-- Open integration obligation: the source-value-zero condition at the centre is
needed because a zero contribution there implements the deleted incoming edge. -/
def RowTermsAgreement : Prop :=
  ∀ (m q : Nat) (Q : MemoryQuotient m q) (plane cap : Phase → Fin q → Nat)
    (X : PairType) (d₀ : Compass) (φ : Phase) (a : Fin q),
    Q.Correct → (X,d₀) ∈ stationaryCases →
    (∀ ψ b, cap ψ b < 2^26 ∧ Fits (plane ψ b) 80 19881 ∧
      lane (plane ψ b) 80 (siteIndex kernelCentre) = 0) →
    ∀ s < 19881, gridSite s ≠ kernelCentre → gridSite s ≠ kernelTarget X →
      component 80 s (rowTerms Q plane cap X d₀ φ a) =
        ∑ d : Compass, ∑ ψ : Phase,
          coefficientCeiling (stationaryCoefficient Q X d₀ φ a (gridSite s) d ψ) *
            (if (gridSite s+d.step) ∈ square (0,0) certificateRadius
             then lane (plane ψ (Q.successor a d)) 80 (siteIndex (gridSite s+d.step))
             else cap ψ (Q.successor a d))

#print axioms localRowCheck_sound
end AKLT.Cert.H3
