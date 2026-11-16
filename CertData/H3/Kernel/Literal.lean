import Lean

namespace AKLT.Cert.H3
open Lean Elab Term

/-- Untrusted elaboration: the result is an ordinary natural number literal. -/
def decodeHexBalanced (s : String) : Nat := Id.run do
  let chars := s.toUTF8
  let rec go : Nat → Nat → Nat → Nat
    | 0, _, _ => 0
    | fuel+1, lo, len =>
      if len ≤ 16 then
        (List.range len).foldl (fun a i =>
          let c := chars[lo+i]!.toNat
          a*16 + if c ≥ 97 then c-87 else c-48) 0
      else
        let left := len/2
        (go fuel lo left <<< (4*(len-left))) + go fuel (lo+left) (len-left)
  return go 64 0 chars.size

syntax (name := h3Hex) "h3_hex% " str : term
@[term_elab h3Hex] def elabH3Hex : TermElab := fun stx _ => do
  let some s := stx[1].isStrLit? | throwError "expected a string"
  unless s.toUTF8.data.all (fun c =>
      (48 ≤ c.toNat && c.toNat ≤ 57) || (97 ≤ c.toNat && c.toNat ≤ 102)) do
    throwError "expected lower-case hexadecimal digits"
  return mkNatLit (decodeHexBalanced s)
end AKLT.Cert.H3
