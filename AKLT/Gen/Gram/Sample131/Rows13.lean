import AKLT.Gen.Gram.Sample131.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

namespace AKLT.Gen.Gram.Sample131
theorem rows13_checked : checkRows lData 1 1 104 m13 l13 = true := by
  decide +kernel
#print axioms rows13_checked
end AKLT.Gen.Gram.Sample131
