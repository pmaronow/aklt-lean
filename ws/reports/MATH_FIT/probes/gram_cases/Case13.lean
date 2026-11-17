module
import Std
public section
namespace MATHFIT.GramCase13
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

def packedM13 : List (Nat × Nat) := [(7,1711628324139566735847629216482007480149191702066286939949301890247908),
(7,1720013170990690031836903500698781199480621951477066360531135106311708),
(7,1657765554653440190064717964389621709176169906068512499904799274369622),
(7,1650747523909482792063387410352996204592858373187813534365896919935828),
(7,1800011750531271209023205644614744341818545012392652557573847457807192),
(7,1812453197211840612020373887044074110612962826475642861995266669352108),
(7,1963259333024194834593426298206402667622329529624888772402659449866212)]
def packedL13 : List (Nat × Nat) := [(1,94773),
(2,9892343792),
(3,1392711162992671),
(4,164121692550337999442),
(5,23869931354729965685106783),
(6,3458831317148758470888028294574),
(7,403475215635401378669522485199436648)]
public theorem checked13 : checkRows (decodeRows 17 packedL13) 1 0 (decodeRows 33 packedM13) (decodeRows 17 packedL13) = true := by decide +kernel
#print axioms checked13

end MATHFIT.GramCase13
