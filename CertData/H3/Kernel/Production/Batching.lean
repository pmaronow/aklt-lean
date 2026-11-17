module
public import CertData.H3.Kernel.Production.Replay

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true
namespace AKLT.Cert.H3.Production
def intervalEnd : Nat → List (Nat × Nat) → Option Nat
  | next, [] => some next
  | next, (start,count)::rest =>
    if start=next ∧ 0<count then intervalEnd (next+count) rest else none
def intervalCheck (parts : List (Nat × Nat)) (limit : Nat) : Bool :=
  intervalEnd 0 parts == some limit
def sumResults (parts : List PrefixResult) : PrefixResult := parts.foldl PrefixResult.add zeroResult
end AKLT.Cert.H3.Production
