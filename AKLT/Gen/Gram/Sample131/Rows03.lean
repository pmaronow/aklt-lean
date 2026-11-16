import AKLT.Gen.Gram.Sample131.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

namespace AKLT.Gen.Gram.Sample131
theorem rows3_checked : checkRows lData 1 1 24 m3 l3 = true := by
  decide +kernel
#print axioms rows3_checked
end AKLT.Gen.Gram.Sample131
