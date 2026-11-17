module
import Std
public section
namespace MATHFIT.GramCase6
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev IntRows := List (List Int)
def dotI : List Int → List Int → Int
 | a::as, b::bs => a*b + dotI as bs
 | _, _ => 0
def residualRow (whole : IntRows) (c : Int) (mr lr : List Int) : List Int :=
 mr.zipWith (fun a l => c*a-dotI lr l) whole
def absSum : List Int → Int
 | [] => 0
 | a::as => Int.ofNat a.natAbs + absSum as
def rowOK (whole : IntRows) (c : Int) (i : Nat) (mr lr : List Int) : Bool :=
 let er := residualRow whole c mr lr
 decide (0 < er.getD i 0) && decide (absSum er < 2 * er.getD i 0)
def checkRows (whole : IntRows) (c : Int) : Nat → IntRows → IntRows → Bool
 | _, [], [] => true
 | i, mr::ms, lr::ls => rowOK whole c i mr lr && checkRows whole c (i+1) ms ls
 | _, _, _ => false

def decodeRow (bits len v : Nat) : List Int :=
  (List.range len).map (fun k => Int.ofNat ((v >>> (k*bits)) &&& (2^bits-1)) - Int.ofNat (2^(bits-1)))
def decodeRows (bits : Nat) (rows : List (Nat × Nat)) : IntRows :=
  rows.map (fun (len,v) => decodeRow bits len v)

def packedM6 : List (Nat × Nat) := [(7,23481787609025634438440054556208815103803578010941923),
(7,19568160290340628350695410415162944596567117982673059),
(7,19568160228953691187631457855753801925104591786551459),
(7,20546567150129849085535595924415565548006676073831578),
(7,24964488246226102457610304621365220644108335122646896),
(7,24964488332913032847247454923526756738373024916080496),
(7,34618196107093637546506872055368072555399912818936720)]
def packedL6 : List (Nat × Nat) := [(1,5489),
(2,48755119),
(3,395845251503),
(4,2897502816907281),
(5,22813050715990395918),
(6,185037909516831836949518),
(7,1392803090981404007701425943)]
public theorem checked6 : checkRows (decodeRows 13 packedL6) 1 0 (decodeRows 25 packedM6) (decodeRows 13 packedL6) = true := by decide +kernel
#print axioms checked6

end MATHFIT.GramCase6
