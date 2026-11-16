import AKLT.Gen.Gram.Sample131.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

namespace AKLT.Gen.Gram.Sample131
theorem rows7_checked : checkRows lData 1 1 56 m7 l7 = true := by
  decide +kernel
#print axioms rows7_checked
end AKLT.Gen.Gram.Sample131
