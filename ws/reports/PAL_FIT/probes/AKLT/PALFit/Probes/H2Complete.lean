import AKLT.Cert.H2.Data

set_option Elab.async false
set_option maxHeartbeats 2000000000
set_option maxRecDepth 1000000

namespace AKLT.PALFit.Probes.H2Complete

/-- Isolated original H2 reduction, with a finite elaboration heartbeat cap. -/
theorem checked : AKLT.Cert.H2.completeCheck = true := by decide +kernel

#print axioms checked
end AKLT.PALFit.Probes.H2Complete
