import AKLT.Gen.Gram.Sample131.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

namespace AKLT.Gen.Gram.Sample131
theorem rows10_checked : checkRows lData 1 1 80 m10 l10 = true := by
  decide +kernel
#print axioms rows10_checked
end AKLT.Gen.Gram.Sample131
