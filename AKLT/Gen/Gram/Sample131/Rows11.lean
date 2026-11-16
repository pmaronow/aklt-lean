import AKLT.Gen.Gram.Sample131.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

namespace AKLT.Gen.Gram.Sample131
theorem rows11_checked : checkRows lData 1 1 88 m11 l11 = true := by
  decide +kernel
#print axioms rows11_checked
end AKLT.Gen.Gram.Sample131
