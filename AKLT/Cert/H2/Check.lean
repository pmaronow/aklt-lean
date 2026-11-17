module
public import AKLT.Cert.H2.Data

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

open AKLT.Defs

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace AKLT.Cert.H2

/-- Kernel reduction of every six-direction code, with all raw rows regenerated. -/
theorem complete_checked : completeCheck = true := by decide +kernel

def rawCodes : Finset (Fin 4096) := Finset.univ.filter (fun c => RawWindow (decodeSix c.val))

theorem raw_codes_count : rawCodes.card = 916 := by decide +kernel

#print axioms complete_checked
#print axioms raw_codes_count
end AKLT.Cert.H2
