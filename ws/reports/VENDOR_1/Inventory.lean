import AKLT.Vendor.All
open Lean Elab Command
elab "#vendorInventory" : command => do
  for (n, c) in (← getEnv).constants.toList do
    if n.toString.startsWith "AKLT.Vendor." then
      let kind := match c with
        | .thmInfo _ => "theorem"
        | .defnInfo _ => "definition"
        | .axiomInfo _ => "postulate"
        | .opaqueInfo _ => "hidden"
        | _ => "generated"
      logInfo m!"VENDOR_DECL {kind} {n}"
#vendorInventory
