module
import Std
public section
namespace MATHFIT.GramCase1
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

def packedM1 : List (Nat × Nat) := [(7,6349997195226338334850904409098865996888849768942557778878108),
(7,6414821757469541954371852000336282941928117358557781523832462),
(7,6108989117455112121114685982387401300211275977129503274912172),
(7,6235428451876075613139907005161577467715317434989377098158664),
(7,6785392757420588314685772722316621415588208060984557117325092),
(7,6671883856757084842885694383182041892908996641083328618491320),
(7,7127825581234284419109305165144793443243031342139543833703328)]
def packedL1 : List (Nat × Nat) := [(1,23133),
(2,645351572),
(3,22631767426396),
(4,659867855928676500),
(5,22649752192424667921221),
(6,889867826483405009308954476),
(7,23324622150573799060008984264223)]
public theorem checked1 : checkRows (decodeRows 15 packedL1) 1 0 (decodeRows 29 packedM1) (decodeRows 15 packedL1) = true := by decide +kernel
#print axioms checked1

end MATHFIT.GramCase1
