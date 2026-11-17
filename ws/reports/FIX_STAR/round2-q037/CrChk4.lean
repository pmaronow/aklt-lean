import AKLT.W.Q037.Main
open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let mods : List String := ["AKLT.W.Q037.Main"]
  let mut out : Array String := #[]
  for (n, _) in env.constants.toList do
    match env.getModuleIdxFor? n with
    | some i => if mods.contains (env.header.moduleNames[i.toNat]!).toString && !n.isInternal then out := out.push n.toString
    | none => pure ()
  IO.FS.writeFile "/home/ubuntu/aklt/reports/FIX_STAR/round2-q037/names.txt" ((String.intercalate "\n" (out.qsort (· < ·)).toList) ++ "\n")
